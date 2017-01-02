(ns cljfst.determinize
  (:gen-class)
  (:require [clojure.pprint :refer [pprint]]
            [clojure.set :refer [union difference intersection]]
            [cljfst.common :refer [cart
                                   powerset
                                   int-to-state
                                   state-to-int
                                   epsilon-symbol]]))

;; This module contains the `subset-construction` function that can determinize
;; an FST.

(defn get-e-reachable
  [state fst]
  (let [e-reachable
        (filter
          (fn [next-state]
            (let [needle
                  (some
                    #{[state epsilon-symbol next-state epsilon-symbol]}
                    (:delta fst))]
              needle))
          (:Q fst))]
    e-reachable))

(defn e-transitionable
  [states fst]
  (let [reachable
        (set
          (apply
            concat
            (map
              (fn [state] (get-e-reachable state fst))
              states)))
        next-reachable
        (set
          (apply
            concat
            (map
              (fn [state] (get-e-reachable state fst))
              reachable)))]
    (if (not-empty (difference next-reachable reachable))
      (e-transitionable (into [] next-reachable) fst)
      reachable)))

(defn E
  [R fst]
  (let [result (e-transitionable R fst)]
    (set (concat R result))))

(defn remove-unreachable
  "Remove unreachable states from the input `intermediate-fst`, i.e., all
  states that are not the initial state or the target of at least one
  transition."
  [intermediate-fst]
  (let [reachable-states
        (reduce
          (fn [reachable transition] (conj reachable (nth transition 2)))
          #{(:s0 intermediate-fst)}
          (:delta intermediate-fst))]
    {:sigma (:sigma intermediate-fst)
     :Q reachable-states
     :s0 (:s0 intermediate-fst)
     :F (intersection reachable-states (:F intermediate-fst))
     :delta (set (filter
              (fn [tr]
                (and (some #{(first tr)} reachable-states)
                     (some #{(nth tr 2)} reachable-states)))
              (:delta intermediate-fst)))}))

;; δ′(R,a) = {q ∈ Q|q ∈ E(δ(r,a)) for some r ∈ R}
(defn get-delta
  [fst Q]
  (reduce
    (fn [delta [sts-i sy-i]]
      (conj
        delta
        [sts-i sy-i
        (E
          (reduce
            (fn [result transition]
              (if (and (some #{(first transition)} sts-i)
                       (= (second transition) sy-i))
                (conj result (nth transition 2))
                result))
            #{}
            (:delta fst)) fst) sy-i]))
    []
    (cart [Q (:sigma fst)])))

(defn get-F
  [Q extant-F]
  (set
    (filter
      (fn [state-set] (some (set state-set) extant-F))
      Q)))

(defn sets->states
  [start-state-set states state-sets index]
  (if (empty? state-sets)
    states
    (let [state-set (first state-sets)]
      (if (= start-state-set state-set)
        (recur start-state-set
               states
               (rest state-sets)
               index)
        (recur start-state-set
              (assoc states state-set (int-to-state index))
              (rest state-sets)
              (inc index))))))

(defn rename-states
  "Convert sets of states to state names (keywords)"
  [fst]
  (let [set->state (sets->states (:s0 fst) {(:s0 fst) :s0} (:Q fst) 1)]
    {:sigma (:sigma fst)
     :Q (set (map (fn [st] (get set->state st)) (:Q fst)))
     :s0 (get set->state (:s0 fst))
     :F (set (map (fn [st] (get set->state st)) (:F fst)))
     :delta (set
              (map
                (fn [tr]
                  [(get set->state (first tr))
                  (second tr)
                  (get set->state (nth tr 2))
                  (nth tr 3)])
                (:delta fst)))}))

(defn determinize
  "Determinization algorithm for FSAs, written by following Dave Bacon's
  handout. WARNING: this will not work with FSTs; use `subset-construction`
  instead."
  [fst]
  (let [Q (powerset (:Q fst))
        delta (into [] (get-delta fst Q))
        F (get-F Q (:F fst))]
    (rename-states
      (remove-unreachable
        {:sigma (:sigma fst)
        :Q Q
        :s0 (E #{(:s0 fst)} fst)
        :F F
        :delta delta}))))

(defn index
  "Return a unique integer for any possible set of state keywords (assumes
  state keywords are of the form `:s` followed by an integer.)"
  [state-set]
  (if (empty? state-set)
    1
    (if (= #{:s0} state-set)
      0
      (Integer.
        (apply str
               (map
                (fn [state] (+ 2 (state-to-int state)))
                state-set))))))

(defn unindex
  "Return a state set, given its corresponding unique integer. Not used, but
  may be useful for debugging."
  [integer]
  (set
    (map
      (fn [dig] (keyword (str "s" (- (Integer. (str dig)) 2))))
      (str integer))))

(def e-closure E)

(defn get-Xs-in-S
  "Get all symbol pairs X with a transition in S"
  [S delta]
  (reduce
    (fn [result [st-i sy-i st-o sy-o]]
      (if (and (not (= epsilon-symbol sy-i))
                (not (= epsilon-symbol sy-o))
                (some #{st-i} S))
        (assoc result [sy-i sy-o]
                (conj (get result [sy-i sy-o] #{}) st-o))
        result))
    {}
    delta))

(defn process-Xs
  "Return a modified `Agenda` and `out-fst` by processing all of the symbol
  pairs X in `Xs`."
  [Xs S Agenda in-fst out-fst processed]
  (reduce
    (fn [result [[sy-i sy-o] moved]]
      (let [T (e-closure moved in-fst)
            index-T (index T)
            result (if (some #{S} processed)
                     result
                     (assoc result :agenda (conj (:agenda result) T)))
            result (assoc-in result
                             [:out-fst :Q]
                             (conj (get-in result [:out-fst :Q])
                                   index-T (index S)))
            in-F (set (:F in-fst)) ;; todo should already be a set...
            out-F (get-in result [:out-fst :F])
            result (if (empty? (intersection T in-F))
                     result
                     (assoc-in result [:out-fst :F]
                               (conj out-F index-T)))
            ;; Add transition δ3(INDEX(S), X, INDEX(T ))
            delta (get-in result [:out-fst :delta])
            result (assoc-in result [:out-fst :delta]
                             (conj delta [(index S) sy-i index-T sy-o]))]
        result))
    {:out-fst out-fst :agenda (set (rest Agenda))}
    Xs))

(defn process-Agenda
  "Process a SubsetConstruction agenda, i.e., a set of sets of states. In the
  process, we modify `out-fst` and possibly add new sets of states to the
  agenda and recur."
  ([Agenda in-fst out-fst] (process-Agenda Agenda in-fst out-fst #{}))
  ([Agenda in-fst out-fst processed]
  (let [S (first Agenda)
        Xs (get-Xs-in-S S (:delta in-fst))
        result (process-Xs Xs S Agenda in-fst out-fst processed)] 
    (if (empty? (:agenda result))
      (:out-fst result)
      (recur (:agenda result)
             in-fst (:out-fst result) (set (conj processed S)))))))

(defn state-ints->kws
  "Convert all state ints in the input `fst` to their corresponding Clojure
  keywords."
  [fst]
  {:sigma (:sigma fst)
   :Q (set (map int-to-state (:Q fst)))
   :s0 (int-to-state (:s0 fst))
   :F (set (map int-to-state (:F fst)))
   :delta (set (map
            (fn [[st-i sy-i st-o sy-o]]
              [(int-to-state st-i)
               sy-i
               (int-to-state st-o)
               sy-o])
            (:delta fst)))})

(defn subset-construction
  "Determinize the input FST via the SubsetConstruction algorithm (cf. Rabin
  and Scott 1959, Hulden 2009 p. 73)."
  [in-fst]
  (let [Agenda #{(e-closure #{(:s0 in-fst)} in-fst)}
        t0 (index (first Agenda))
        out-fst {:sigma (:sigma in-fst)
                 :Q #{}
                 :s0 t0
                 :F #{}
                 :delta #{}}
        new-fst (process-Agenda Agenda in-fst out-fst)]
    (remove-unreachable
      (state-ints->kws new-fst))))
