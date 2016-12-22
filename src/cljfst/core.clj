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


(def regex-stmt
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

(defn create-mapping
  "Create a simple FST that maps symbol `left` to symbol `right`"
  [[left right]]
  {:sigma (into [] (set [left right]))
   :Q [:s0 :s1]
   :s0 :s0
   :F [:s1]
   :delta [[:s0 left :s1 right]]})

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

(defn regex-to-fst
  "Convert the regular expression `regex` to an FST (hash)"
  [fst regex]
  ;; (println "DEBUG turning this regex into an FST:")
  ;; (clojure.pprint/pprint regex)
  ;; (println "in regex-to-fst with regex " regex " and fst " fst)
  (cond
    (= :regex-stmt regex) fst
    (some #{(first regex)} #{:regex-cmd :stmt-trmntr}) fst
    (string? regex) (regex-to-fst {} [:mapping regex regex])
    (= :mapping (first regex)) (create-mapping (rest regex))
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

(defn -main
  "Provide an AT&T-formatted FST path and an input string and behold the
  apply-down-ness!"
  [& args]
  (let [parse (regex-stmt (first args))
        fst (parse-to-fst parse)]
    (clojure.pprint/pprint parse)
    (clojure.pprint/pprint fst)
    (println (clojure.string/join ", " (apply-down fst (second args)))))
  ;; (println (apply-down (parse-att (first args)) (second args)))
)
