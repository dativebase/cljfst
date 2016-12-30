(ns cljfst.determinize
  (:gen-class)
  (:require [clojure.pprint :refer [pprint]]
            [clojure.set :refer [union difference intersection]]
            [cljfst.common :refer [cart
                                   int-to-state]]))

(defn powerset [ls]
  (if (empty? ls) #{#{}}
    (union (powerset (next ls))
           (map #(conj % (first ls)) (powerset (next ls))))))

(def epsilon-symbol "@0@")

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
  [intermediate-fst]
  (let [reachable-states
        (reduce
          (fn [reachable transition] (conj reachable (nth transition 2)))
          #{}
          (:delta intermediate-fst))]
    {:sigma (:sigma intermediate-fst)
     :Q reachable-states
     :s0 (:s0 intermediate-fst)
     :F (intersection reachable-states (:F intermediate-fst))
     :delta (filter
              (fn [tr]
                (and (some #{(first tr)} reachable-states)
                     (some #{(nth tr 2)} reachable-states)))
              (:delta intermediate-fst))}))

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
