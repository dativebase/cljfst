(ns cljfst.minimize
  (:gen-class)
  (:require [clojure.pprint :refer [pprint]]
            [clojure.set :refer [difference]]
            [cljfst.common :refer [cart]]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Hopcroft Canonical Minimization Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn incoming-transition
  "Return true if you can use `symbol` to transition into one of the states in
  `states` using `transition`."
  [transition symbol states]
  (if (and (= symbol (second transition))
           (some #{(nth transition 2)} states))
    true
    false))

(defn fewest-incoming-transitions
  "Return whichever of final-states or non-final-states has the fewest incoming
  transitions to symbol, given delta."
  [delta symbol final-states non-final-states]
  (let [into-final
        (filter (fn [x] (incoming-transition x symbol final-states)) delta)
        into-non-final
        (filter (fn [x] (incoming-transition x symbol non-final-states)) delta)]
    (if (< (count into-final) (count into-non-final))
      final-states
      non-final-states)))

(defn get-hcc-agenda
  "Return Hopcroft canonical agenda: a vector of 2-ary vectors where the first
  element is a vector of states (the final states or the non-final ones) and the
  second one is a symbol in sigma. The vector of states chose is what which has
  fewer incoming transitions for the symbol in question."
  [final-states non-final-states sigma delta]
  (reduce
    (fn [container symbol]
      (conj container
            [(fewest-incoming-transitions delta symbol final-states
                                          non-final-states)
             symbol]))
    []
    sigma))

(defn get-incoming-transitions
  "Return incoming transitions for a Hopcroft canonical agenda item, where an
  agenda item is a block (vector) of states and a symbol; that is, return a
  mapping from each state `s` to all transitions such that one of the states in
  `block` is accessible from state `s` by reading in symbol `symbol`."
  [block symbol fst]
  (into
    {}
    (map
      (fn [state]
        [state
          (filter
            (fn [transition]
              (let [pred (and (= (first transition) state)
                              (= (second transition) symbol)
                              (some #{(nth transition 2)} block))]
                pred))
            (:delta fst))])
      (:Q fst))))

(defn get-new-Pi-and-splits
  "Returns a hash mapping `:new-Pi` to a vector of vectors of states (a
  new partition of the states in an FST) and `:splits` to a vector of
  vectors, each containing a partition (of states) as first element and a 2-ary
  sub-partition of that partition, the first being those states that are
  'incoming' given `incoming-transition` and the second being those that are
  not."
  [Pi incoming-transitions]
  (let [new-Pi-and-splits
        (reduce
          (fn [container partition]
            ;; `partition` is a vector of states
            (if (> (count partition) 1)
              ;; split partition into those in incoming-transitions and those not.
              (let [{subpart-incoming true subpart-non-incoming false}
                    (group-by
                      (fn [x] (> (count (get incoming-transitions x)) 0))
                      partition)]
                (if (and subpart-incoming subpart-non-incoming)
                  (assoc
                    (assoc container :new-Pi
                          (conj (:new-Pi container) subpart-incoming
                                subpart-non-incoming))
                    :splits
                    (conj (:splits container) [partition [subpart-incoming
                                                          subpart-non-incoming]]))
                  (assoc container :new-Pi (conj (:new-Pi container)
                                                 partition))))
              ;; elsewhere case: partition is un-split-able
              (assoc container :new-Pi (conj (:new-Pi container) partition))))
          {:new-Pi [] :splits []}
          Pi)]
    new-Pi-and-splits))

(defn get-agenda-item-size
  "Return the size of an agenda item. An agenda item is a vector of states and
  a symbol in sigma of an FST. Its size is the number of transitions that will
  allow one to enter one of the states in the vector by reading in the symbol."
  [[states symbol] delta]
  (reduce + (map
              (fn [state]
                (count
                  (filter
                    (fn [transition]
                      (and
                        (= symbol (second transition))
                        (= state (nth transition 2))))
                    delta)))
              states)))

(defn get-hcc-min
  "Get the Min of two candidate agenda items, i.e., the one with the smallest
  size, according to `get-agenda-item-size`."
  [cand1 cand2 delta]
  (let [cand1-size
        (get-agenda-item-size cand1 delta)
        cand2-size
        (get-agenda-item-size cand2 delta)]
    (if (< cand1-size cand2-size) cand1 cand2)))

(defn get-agenda-mods
  "Return a hash map of agenda modifications (for the Hopcroft canonical
  minimization algorithm) based on the vector of new splits."
  [new-splits fst hcc-agenda]
  (let [result
    (reduce
      (fn [container [split symbol]]
        (let [[partition [subpart-incoming subpart-non-incoming]] split]
          ;; if the partition-symbol pair is on agenda...
          (if (some #{[partition symbol]} hcc-agenda)
            ;; ... add to :replace-on-agenda a 2-ary vector whose first element
            ;; is the to-be-replaced agenda item and whose second element is a
            ;; vector of replacement agenda items.
            (assoc container :replace-on-agenda
                  (conj (:replace-on-agenda container)
                        [[partition symbol] [[subpart-incoming symbol]
                                              [subpart-non-incoming symbol]]]))
            ;; otherwise, add to agend the "Min" of `[subpart-incoming symbol]`
            ;; and `[subpart-non-incoming symbol]`, where "Min" means ...
            (let [min (get-hcc-min [subpart-incoming symbol]
                                   [subpart-non-incoming symbol]
                                   (:delta fst))]
              (assoc container :add-to-agenda (conj (:add-to-agenda container)
                                                    min))))))
    {:replace-on-agenda [] :add-to-agenda []}
    (cart [new-splits (:sigma fst)]))]
    result))

(defn get-new-hcc-agenda
  "Get a new Hopcroft canonical agenda, given the existing agenda and a hash
  map of modifications to make. The agenda is a vector of items to be
  processed/consumed in the course of minimization."
  [hcc-agenda agenda-mods]
  (let [result
        (reduce
          (fn [new-agenda existing-agenda-item]
            (let [replacement
                  (first (filter (fn [mapping] (= (first mapping)
                                                  existing-agenda-item))
                                (:replace-on-agenda agenda-mods)))]
              (if replacement
                (concat new-agenda (second replacement))
                (conj new-agenda existing-agenda-item))))
          (:add-to-agenda agenda-mods)
          hcc-agenda)]
    result))

(defn agenda-to-equiv-classes
  "Takes a Hopcroft canonical minimization agenda (a vector containing 2-ary
  vectors, which each contain a vector of states and a symbol from the
  alphabet) and Pi, a partitioning of the states in a given FST, and returns Pi
  as a set of equivalence classes of states, i.e., states that are equivalent
  and can be merged in order to accomplish minimization."
  [fst hcc-agenda Pi]
  (let [agenda-item (first hcc-agenda)]
    (if agenda-item
      ;; examine the first agenda item
      (let [[block symbol] agenda-item
            ;; maps states to vectors of their incoming transitions to any
            ;; state in `block` via `symbol`
            incoming-transitions (get-incoming-transitions block symbol fst)]
        (if (> (reduce + (map count (vals incoming-transitions))) 0)
          (let [new-Pi-and-splits
                (get-new-Pi-and-splits Pi incoming-transitions)
                agenda-mods
                (get-agenda-mods (:splits new-Pi-and-splits) fst hcc-agenda)
                new-hcc-agenda
                (get-new-hcc-agenda (rest hcc-agenda) agenda-mods)]
            (recur fst new-hcc-agenda (:new-Pi new-Pi-and-splits)))
            (recur fst (rest hcc-agenda) Pi)))
      Pi)))

(defn hopcroft-canonical-equiv-classes
  "Perform Hopcroft canonical minimization on `fst`, cf. Hulden p. 80. Takes an
  FST as input and returns Pi, a set of equivalence classes, i.e., sets of
  states that are equivalent and can be merged."
  [fst]
  (let [final-states (:F fst)
        non-final-states (into []
                               (difference
                                 (set (:Q fst))
                                 (set final-states)))
        Pi [final-states non-final-states]
        hcc-agenda
        (get-hcc-agenda final-states non-final-states (:sigma fst) (:delta
                                                                     fst))]
    (agenda-to-equiv-classes fst hcc-agenda Pi)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Hopcroft Optimized Minimization Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; WARNING: I have been unable to implement Hulden's "Optimized" Hopcroft
;; minimization algorithm. `hopcroft-optimized-equiv-classes` will not work.

(defn block-is-accessible
  "Return a truthy value if a given block of states is accessible by reading in
  a given symbol, given the transition matrix in a given fst.
  `incoming-transitions` maps states to vectors of transitions that will allow
  movement into a state in the given block via the givne symbol."
  [incoming-transitions]
  (> (reduce + (map count (vals incoming-transitions))) 0))

(defn get-agenda-mods-hco
  [new-splits fst hco-agenda block index symbol]
  (let [result
    (reduce
      (fn [container split]
        (let [[partition [subpart-incoming subpart-non-incoming]] split]
          ;; if the partition (B) = block
          (if (= partition block)
            (let [min (get-hcc-min [subpart-incoming symbol]
                                   [subpart-non-incoming symbol]
                                   (:delta fst))
                  min [(first min) 0]
                  max (if (= subpart-incoming (first min))
                        [subpart-non-incoming index]
                        [subpart-incoming index])]
              (assoc container :add-to-agenda (conj (:add-to-agenda container)
                                                    min max)))
            ;; if the partition-symbol pair is on agenda...
            (if (some #{[partition index]} hco-agenda)
              ;; ... add to :replace-on-agenda a 2-ary vector whose first
              ;; element is the to-be-replaced agenda item and whose second
              ;; element is a vector of replacement agenda items.
              (assoc container :replace-on-agenda
                    (conj (:replace-on-agenda container)
                          [[partition index] [[subpart-incoming 0]
                                              [subpart-non-incoming 0]]]))
              ;; otherwise, add to agend the "Min" of `[subpart-incoming
              ;; symbol]` and `[subpart-non-incoming symbol]`
              (let [min (get-hcc-min [subpart-incoming symbol]
                                     [subpart-non-incoming symbol]
                                     (:delta fst))]
                (assoc container :add-to-agenda (conj (:add-to-agenda container)
                                                      [(first min) 0])))))))
      {:replace-on-agenda [] :add-to-agenda []}
      new-splits)]
    result))

(defn agenda-to-equiv-classes-hco
  "Takes a Hopcroft optimized minimization agenda (a vector containing 2-ary
  vectors, which each contain a vector of states and an index in sigma) and Pi,
  a partitioning of the states in a given FST, and returns Pi as a set of
  equivalence classes of states, i.e., states that are equivalent and can be
  merged in order to accomplish minimization."
  [fst hco-agenda Pi]
  (let [C (first hco-agenda)]
    (if C
      ;; examine the first agenda item
      (let [[block index] C
            symbol (get (:sigma fst) index)
            incoming-transitions (get-incoming-transitions block symbol fst)]
        (if (block-is-accessible incoming-transitions)
          (let [new-Pi-and-splits
                (get-new-Pi-and-splits Pi incoming-transitions)
                agenda-mods
                (get-agenda-mods-hco (:splits new-Pi-and-splits) fst hco-agenda
                                     block index symbol)
                new-hco-agenda
                (get-new-hcc-agenda (rest hco-agenda) agenda-mods)]
            (recur fst new-hco-agenda (:new-Pi new-Pi-and-splits)))
          (recur fst (rest hco-agenda) Pi)))
        Pi)))

(defn hopcroft-optimized-equiv-classes
  "Get state equivalence classes, via the 'optimized' Hopcroft minimization
  algorithm on `fst`, cf. Hulden p. 84. Takes an FST as input and returns Pi, a
  set of equivalence classes, i.e., sets of states that are equivalent and can
  be merged.
  "
  [fst]
  (let [final-states (:F fst)
        non-final-states (into []
                               (difference
                                 (set (:Q fst))
                                 (set final-states)))
        Pi [final-states non-final-states]
        hco-agenda
        (map
          (fn [x] (into [] x))
          (cart
            [[final-states non-final-states]
              (range (count (:sigma fst)))]))]
    (agenda-to-equiv-classes-hco fst hco-agenda Pi)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General Minimization Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn get-minimize-fixer
  "Return a hash mapping each state in `Q` to a replacement state, given the
  vector of vectors of equivalent states in `equiv-classes`."
  [equiv-classes Q]
  (let [fixers (filter #(> (count %) 1) equiv-classes)]
    (reduce
      (fn [container state]
        (if (= state :s0)
          (assoc container state state)
          (let [fixer (first (filter #(some #{state} %) fixers))]
            (if fixer
              (assoc container state (first fixer))
              (assoc container state state)))))
      {}
      Q)))

(defn minimize-state-set
  "Minimize a vector of states; i.e., remove the redundant ones, given a
  `fixer` hash derived from a minimization algorithm."
  [state-set fixer]
  (into [] (set (map (fn [state] (get fixer state state)) state-set))))

(defn minimize-delta
  "Minimize delta (the transition matrix of an FST), given `fixer` a mapping
  from states to their replacements."
  [delta fixer]
  (into [] (set (map (fn [[st-i sy-i st-o sy-o]]
         [(get fixer st-i st-i)
          sy-i
          (get fixer st-o st-o)
          sy-o])
       delta))))

(defn minimize-hcc
  "Perform Hopcroft canonical minimization."
  [fst]
  (let [equiv-classes (hopcroft-canonical-equiv-classes fst)
        fixer (get-minimize-fixer equiv-classes (:Q fst))]
    {:sigma (:sigma fst)
     :Q (minimize-state-set (:Q fst) fixer)
     :s0 :s0
     :F (minimize-state-set (:F fst) fixer)
     :delta (minimize-delta (:delta fst) fixer)}))
