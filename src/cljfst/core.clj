(ns cljfst.core
  (:gen-class)
  (:require clojure.pprint)
  (:require clojure.set)
  (:require clojure.string)
  (:require [instaparse.core :as insta]))


(def test-fst
  {:sigma ["a" "b" "c" "d"]    ;; alphabet
   :Q [:s0 :s1 :s2 :s3]        ;; all states (not used)
   :s0 :s0                     ;; initial state (redundant?)
   :F [:s0 :s1 :s2]            ;; final states
   :delta [[:s0 "@" :s0 "@"]  ;; transition matrix
           [:s0 "a" :s0 "a"]
           [:s0 "b" :s0 "b"]
           [:s0 "c" :s1 "c"]
           [:s0 "d" :s0 "d"]
           [:s1 "@" :s0 "@"]
           [:s1 "a" :s2 "a"]
           [:s1 "a" :s3 "b"]
           [:s1 "b" :s0 "b"]
           [:s1 "c" :s1 "c"]
           [:s1 "d" :s0 "d"]
           [:s2 "@" :s0 "@"]
           [:s2 "a" :s0 "a"]
           [:s2 "b" :s0 "b"]
           [:s2 "c" :s1 "c"]
           [:s3 "d" :s0 "d"]]})

(def unknown-symbol "@_UNKNOWN_SYMBOL_@")
(def epsilon-symbol "@0@")
(def identity-symbol "@_IDENTITY_SYMBOL_@")

(defn get-transitions
  "Return a seq of out-state/out-symbol pairs for the given in-state/in-symbol
  pair in the given fst"
  [fst in-st in-sym]
  (filter
    #(and (= in-st (first %))
          (or (= "0" (second %)) (= in-sym (second %))))
    (:delta fst)))

(defn apply-down
  "Perform the apply down transformation on string `input` using the FST `fst`"
  ([fst input] (apply-down fst input (:s0 fst) [""]))
  ([fst input state outputs]
    (if (and (some #{state} (:F fst))
             (clojure.string/blank? input))
        outputs
        (let [inpchr (str (first input))]
          (let
            [keychr (if (some #{inpchr} (:sigma fst)) inpchr "@")
              transitions (get-transitions fst state keychr)]
            (reduce concat
                    []
                    (map (fn
                            [[curr-state curr-sym next-state next-char]]
                            (apply-down
                              fst
                              (if (= "0" curr-sym) input (apply str (rest input)))
                              next-state
                              (map
                                #(str % (get {"@" inpchr "0" ""} next-char next-char))
                                outputs)))
                          transitions)))))))

(defn states-syms-att
  "Input: len-4 vector from AT&T line; output: vector of keywords (states) and
  strings (FST symbols)"
  [fields]
  (map-indexed
    (fn [idx itm]
      (if (< idx 2)
        (keyword (str "s" itm))
        (if (= itm "@_IDENTITY_SYMBOL_@")
          "@"
          (if (= itm "@0@")
            ""
            itm))))
    fields))

(defn process-line-att [line]
  "Process AT&T FST line: 4 tab-separated vals means input state, output state,
  input symbol, output symbol. One value means final state"
  (let [fields (clojure.string/split line #"\t")]
    (if (> (count fields) 3)
      (let [[st-i st-o sym-i sym-o] (states-syms-att fields)]
        {:delta [st-i sym-i st-o sym-o]
         :sigma [sym-i sym-o]})
      {:F [(keyword (str "s" (first fields)))]})))

(defn add-att-line-to-fst
  "Return a new `fst` hash built by updating the passed-in one with the AT&T
  line"
  [fst line]
  (let [p-l (process-line-att line)]
    (assoc
      (assoc
        (assoc fst :delta (conj (:delta fst) (:delta p-l)))
        :sigma
        (into [] (set (into (:sigma fst) (get p-l :sigma [])))))
      :F
      (into [] (set (into (:F fst) (get p-l :F [])))))))


(defn parse-att
  "Parse AT&T-formatted FST file at `file-path` and return an FST hash map."
  [file-path]
  (with-open [rdr (clojure.java.io/reader file-path)]
    (reduce
      add-att-line-to-fst
      {:sigma []  ;; alphabet
       :Q []  ;; all states
       :s0 :s0  ;; designated start state
       :F []  ;; final states
       :delta []  ;; vector of vectors: [[st-i sym-i st-o sym-o] ...]
      }
      (line-seq rdr))))


;; The parser is defined in resources/grammar.bn. It is a CFG defined via the
;; context-free rewrite rules and Clojure library instaparse.
(def read-regex
  (insta/parser (clojure.java.io/resource "grammar.bnf")))

(defn state-to-int
  "Convert an FST state keyword (like :s1) to an integer (like 1)"
  [state-keyword]
  (Integer. (apply str (nthrest (str state-keyword) 2))))

(defn int-to-state
  "Convert an integer (like 1) to an FST state keyword (like :s1)"
  [state-int]
  (keyword (str "s" state-int)))

(defn inc-state
  "Increment a state (keyword) and return it as a keyword"
  [state-keyword]
  (int-to-state (inc (state-to-int state-keyword))))

(defn sigma-from-mapping
  [sym-i sym-o]
  (if (some #{unknown-symbol} [sym-i sym-o])
    (into [] (set [sym-i sym-o identity-symbol]))
    (into [] (set [sym-i sym-o]))))

(defn delta-from-mapping
  [sym-i sym-o]
  (cond
    (= sym-o unknown-symbol) [[:s0 sym-i :s1 sym-o] [:s0 sym-i :s1 sym-i]]
    (= sym-i unknown-symbol) [[:s0 sym-i :s1 sym-o] [:s0 sym-o :s1 sym-o]]
    :else [[:s0 sym-i :s1 sym-o]]))

(defn create-mapping
  "Create a simple FST that maps symbol `sym-i` to symbol `sym-o`"
  ([sym] (create-mapping sym sym))
  ([sym-i sym-o]
    (let [sigma (sigma-from-mapping sym-i sym-o)
          delta (delta-from-mapping sym-i sym-o)]
      {:sigma sigma
      :Q [:s0 :s1]
      :s0 :s0
      :F [:s1]
      :delta delta})))

(defn get-unique-states
  "Return a hash map mapping states in target-states to states not in
  conflictee-states"
  ([target-states conflictee-states] (get-unique-states target-states conflictee-states target-states))
  ([target-states conflictee-states candidates]
    ;; (println "make states " target-states " not conlfict with " conflictee-states)
    (let [new-candidates
          (into [] (map (fn [state] (int-to-state (inc (state-to-int state))))
                        candidates))]
      (if (not-empty (clojure.set/intersection (set new-candidates) (set conflictee-states)))
        (get-unique-states target-states conflictee-states new-candidates)
        (zipmap target-states new-candidates)))))

(defn remove-state-conflicts
  "Return a new FST based on `target-fst` but where all states are renamed so
  that no states in `target-fst` are also in `conflictee-fst`"
  [target-fst, conflictee-fst]
  (let [state-fixer (get-unique-states (:Q target-fst) (:Q conflictee-fst))]
    ;; (println "\nstate-fixer")
    ;; (println state-fixer)
    ;; (println "\n")
    {:sigma (into [] (set (concat (:sigma target-fst) (:sigma conflictee-fst))))
     :Q (into [] (vals state-fixer))
     :s0 ((:s0 target-fst) state-fixer)
     :F (into [] (map #(% state-fixer) (:F target-fst)))
     :delta (into [] (map
                       (fn [[st-i sym-i st-o sym-o]]
                         (let [st-i-fixed (st-i state-fixer)
                               st-o-fixed (st-o state-fixer)]
                           ;; (println "fixing " st-i " to " st-i-fixed)
                           ;; (println "fixing " st-o " to " st-o-fixed)
                           [(st-i state-fixer)
                            sym-i
                            (st-o state-fixer)
                            sym-o]))
                       (:delta target-fst)))}))

(defn concatenate
  "Concatenate two FSTs:
  - rename states in fst2 so no conflicts with fst1
  - add transitions from all final states in L1 to the initial state in L2
  - make all states in L1 nonfinal
  - make initial state of L1 the initial state of L3"
  [[fst1 fst2]]
  ;; (println "DEBUG concatenate")
  ;; (println "fst1")
  ;; (clojure.pprint/pprint fst1)
  ;; (println "fst2")
  ;; (clojure.pprint/pprint fst2)
  ;; (println "\n")
  (let [fst2-no-confl (remove-state-conflicts fst2 fst1)]
    ;; (println "fst2-no-confl")
    ;; (clojure.pprint/pprint fst2-no-confl)
    ;; (println "\n")
    (let [tmp
          (assoc
            (reduce
              (fn [fst final-state]
                (assoc fst :delta (conj (:delta fst) [final-state "0" (:s0 fst) "0"])))
              fst2-no-confl
              (:F fst1))
            :s0
            :s0)]
      (assoc
        (assoc tmp :Q (into [] (set (concat (:Q fst1 ) (conj (:Q tmp) :s0)))))
        :delta
        (into [] (concat (:delta tmp) (:delta fst1)))))))

(defn inc-all-states
  "Increment all states in fst"
  [fst]
  {:sigma (:sigma fst)
   :Q (into [] (map inc-state (:Q fst)))
   :s0 (inc-state (:s0 fst))
   :F (into [] (map inc-state (:F fst)))
   :delta (into [] (map (fn
                          [[st-i sy-i st-o sy-o]]
                          [(inc-state st-i)
                           sy-i
                           (inc-state st-o)
                           sy-o])
                        (:delta fst)))})

(defn perform-union
  "Perform the union operation on two FSTs: fst1 and fst2
  - create a new fst fst3
  - add an initial state to fst3 with epsilon-transitions to the initial states
    of L1 and L2."
  [[fst1 fst2]]
  ;; (println "DEBUG perform-union")
  ;; (println "fst1")
  ;; (clojure.pprint/pprint fst1)
  ;; (println "fst2")
  ;; (clojure.pprint/pprint fst2)
  ;; (println "\n")
  (let [fst2-no-confl (remove-state-conflicts fst2 fst1)
        fst1 (inc-all-states fst1)
        fst2 (inc-all-states fst2-no-confl)]
    {:sigma (:sigma fst2)
     :Q (into [] (set (concat (:Q fst1) (:Q fst2) [:s0])))
     :s0 :s0
     :F (into [] (set (concat (:F fst1) (:F fst2))))
     :delta (into [] (set (concat (:delta fst1)
                             (:delta fst2)
                             (map
                               (fn [prev-init-st]
                                 [:s0 "0" prev-init-st "0"])
                               [(:s0 fst1) (:s0 fst2)]))))}))

(defn kleene-star-repeat
  "- add a new initial state which is also final with epsilon-transition(s) to
     the formerly initial states
   - add epsilon-transitions from all final states in L1 to the new initial
     state"
  [fst]
  ;; (println "in kleene-star-repeat with " fst)
  (let [tmp-fst (inc-all-states fst)
        prev-final-states (:F tmp-fst)]
    {:sigma (:sigma tmp-fst)
     :Q (conj (:Q tmp-fst) :s0)
     :s0 :s0
     :F [:s0]
     :delta (concat (:delta tmp-fst)
                    [[:s0 "0" :s1 "0"]]
                    (into []
                          (map (fn [prev-final-state]
                                 [prev-final-state "0" :s0 "0"])
                               prev-final-states)))}))

(defn process-regex-symbol
  [[symbol-parse]]
  ;; (println "SYMBOL PARSE" symbol-parse)
  (cond
    (= :atomic-symbol (first symbol-parse)) (second symbol-parse)
    (= :wildcard (first symbol-parse)) unknown-symbol
    (= :nil-symbol (first symbol-parse)) epsilon-symbol
    (= :identity-symbol (first symbol-parse)) identity-symbol))

(defn regex-to-fst
  "Convert the regular expression `regex` to an FST (hash)"
  [fst regex]
  ;; (println "DEBUG turning this regex into an FST:")
  ;; (clojure.pprint/pprint regex)
  ;; (println "in regex-to-fst with regex " regex " and fst " fst)
  (cond
    (= :regex-stmt regex) fst
    (some #{(first regex)} #{:regex-cmd :stmt-trmntr}) fst
    (= :symbol (first regex)) (process-regex-symbol (rest regex))
    (string? regex) (regex-to-fst {} [:mapping regex regex])
    (= :mapping (first regex)) (apply create-mapping (map #(regex-to-fst {} %) (rest regex)))
    (= :concatenation (first regex)) (concatenate (map #(regex-to-fst {} %) (rest regex)))
    (= :union (first regex)) (perform-union (map #(regex-to-fst {} %) (rest regex)))
    (= :kleene-star-repetition (first regex)) (kleene-star-repeat (regex-to-fst {} (second regex)))
  )
)

(defn parse-to-fst
  "Take an instaparse parse of a regex expression and return an FST"
  [parse]
  ;; (println parse)
  ;; [:regex-stmt [:regex-cmd "regex"] [:mapping "a" "b"] [:stmt-trmntr ";"]]
  (reduce
    regex-to-fst
    {}
    parse))

;; Notes
;; - a @:@ transition signifies any identity pair not in the currently declared
;;   alphabet
;; - the ?-symbol on one side of a symbol pair signifies any symbol also not in
;;   the alphabet
;; - the combination ?:? is reserved for the non-identity relation of any
;;   symbol pair where each symbol is outside the alphabet.

(defn merge-alphabet
  [cont-vec [fst N]]
  (into cont-vec [[fst N]]))

(defn merge-alphabets
  "Merge the alphabets of two fsts. Takes two fsts and returns them, with
  modified alphabets."
  [fst1 fst2]
  (let [N-1 (filter (fn [x] (not (some #{x} (:sigma fst1)))) (:sigma fst2))
        N-2 (filter (fn [x] (not (some #{x} (:sigma fst2)))) (:sigma fst1))]
    (reduce
      merge-alphabet
      []
      [[fst1 N-1] [fst2 N-2]])))

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
  (let [into-final (filter
                     (fn [x] (incoming-transition x symbol final-states)) delta)
        into-non-final (filter
                         (fn [x] (incoming-transition x symbol non-final-states))
                         delta)]
    (if (< (count into-final) (count into-non-final))
      final-states
      non-final-states)))

(defn get-hcc-agenda
  "Return Hopcroft canonical agenda: for each symbol in sigma, return
  final-states or non-final-states, depending on which has fewer incoming
  transitions for that symbol"
  [final-states non-final-states sigma delta]
  (reduce
    (fn [container symbol]
      (conj container
            [(fewest-incoming-transitions delta symbol final-states
                                         non-final-states)
             symbol]))
    []
    sigma))

(defn count-incoming-transitions-from-state
  [fst symbol state]
  (reduce
    +
    (count (filter
      (fn [transition]
        (and (= symbol (second transition))
           (= state (nth transition 2))))
      (:delta fst)))))

(defn count-incoming-transitions-from-states
  "Return the number of incoming transitions into all states in `states` using
  where `symbol` ."
  [fst symbol states]
  (reduce
    +
    (map
      (fn [state]
          (count-incoming-transitions-from-state fst symbol state))
      states)))

(defn get-incoming-transitions
  "Return incoming transitions for a Hopcroft canonical agenda item, i.e., a
  block (vector) of states and a symbol; that is, return a mapping from each
  state `s` to all transitions such that one of the states in `block` is
  accessible from state `s` by reading in symbol `symbol`."
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
                (assoc
                  (assoc container :new-Pi
                        (conj (:new-Pi container) subpart-incoming
                              subpart-non-incoming))
                  :splits
                  (conj (:splits container) [partition [subpart-incoming
                                                        subpart-non-incoming]])))
              ;; elsewhere case: partition is un-split-able
              (assoc container :new-Pi (conj (:new-Pi container) partition))))
          {:new-Pi [] :splits []}
          Pi)]
    new-Pi-and-splits))

(defn get-agenda-item-size
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
  [cand1 cand2 delta]
  (let [cand1-size
        (get-agenda-item-size cand1 delta)
        cand2-size
        (get-agenda-item-size cand2 delta)]
    (if (< cand1-size cand2-size) cand1 cand2)))

(defn cart [colls]
  (if (empty? colls)
    '(())
    (for [x (first colls)
          more (cart (rest colls))]
      (cons x more))))

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
  [hcc-agenda agenda-mods]
  (reduce
    (fn [new-agenda existing-agenda-item]
      (let [replacement
            (first (filter (fn [mapping] (= (first mapping)
                                            existing-agenda-item))
                           (:replace-on-agenda agenda-mods)))]
        (if replacement
          (concat new-agenda replacement)
          (conj new-agenda existing-agenda-item))))
    (:add-to-agenda agenda-mods)
    hcc-agenda))

(defn agenda-to-equiv-classes
  "Takes a Hopcroft canonical agenda (a vector containing 2-vectors, which each
  contain a vector of states and a symbol from the alphabet) and Pi, a
  partitioning of the states in a given FST, and returns Pi as a set of
  equivalence classes of states, i.e., states that are equivalent and can be
  merged."
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
                               (clojure.set/difference
                                 (set (:Q fst))
                                 (set final-states)))
        Pi [final-states non-final-states]
        hcc-agenda
        (get-hcc-agenda final-states non-final-states (:sigma fst) (:delta
                                                                     fst))]
    (agenda-to-equiv-classes fst hcc-agenda Pi)))

(defn get-minimize-fixer
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
  [state-set fixer]
  (into [] (set (map (fn [state] (get fixer state state)) state-set))))

(defn minimize-delta
  [delta fixer]
  (into [] (set (map (fn [[st-i sy-i st-o sy-o]]
         [(get fixer st-i st-i)
          sy-i
          (get fixer st-o st-o)
          sy-o])
       delta))))

(defn minimize-hcc
  [fst]
  (let [equiv-classes (hopcroft-canonical-equiv-classes fst)
        fixer (get-minimize-fixer equiv-classes (:Q fst))]
    {:sigma (:sigma fst)
     :Q (minimize-state-set (:Q fst) fixer)
     :s0 :s0
     :F (minimize-state-set (:F fst) fixer)
     :delta (minimize-delta (:delta fst) fixer)}))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; END Hopcroft Canonical Minimization Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn -main
  "Provide an AT&T-formatted FST path and an input string and behold the
  apply-down-ness!"
  [& args]
  (let [input-regex (first args)
        parse (read-regex input-regex)
        fst (parse-to-fst parse)]
    (clojure.pprint/pprint parse)
    (clojure.pprint/pprint fst)
    (println (clojure.string/join ", " (apply-down fst (second args)))))
  ;; (println (apply-down (parse-att (first args)) (second args)))
)
