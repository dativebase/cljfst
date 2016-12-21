(ns cljfst.core
  (:gen-class)
  (:require clojure.pprint)
  (:require [instaparse.core :as insta]))



(def test-fst
  {:sigma ["a" "b" "c" "d"]    ;; alphabet
   :Q [:s0 :s1 :s2 :s3]        ;; all states (not used)
   :s0 :s0                     ;; initial state (redundant?)
   :F [:s0 :s1 :s2]            ;; final states
   :delta {:s0 {"@" {:s0 "@"}  ;; transition matrix
                "a" {:s0 "a"}
                "b" {:s0 "b"}
                "c" {:s1 "c"}
                "d" {:s0 "d"}}
           :s1 {"@" {:s0 "@"}
                "a" {:s2 "a"
                     :s3 "b"}
                "b" {:s0 "b"}
                "c" {:s1 "c"}
                "d" {:s0 "d"}}
           :s2 {"@" {:s0 "@"}
                "a" {:s0 "a"}
                "b" {:s0 "b"}
                "c" {:s1 "c"}}
           :s3 {"d" {:s0 "d"}}}})


(defn apply-down
  "Perform the apply down transformation on string `input` using the FST `fst`"
  ([fst input] (apply-down fst input (:s0 fst) [""]))
  ([fst input state outputs]
    (let [inpchr (str (first input))]
      (if-not (clojure.string/blank? inpchr)
        (do
          (if (some #{inpchr} (:sigma fst))
            (def keychr inpchr)
            (def keychr "@"))
          (def next-states (get-in (:delta fst) [state keychr]))
          (if next-states
            (reduce concat
                    []
                    (map (fn
                           [[next-state next-char]]
                           (apply-down
                             fst
                             (rest input)
                             next-state
                             (map
                               #(str % (get {"@" inpchr} next-char next-char))
                               outputs)))
                         next-states))
            []))
        (if (some #{state} (:F fst))
          outputs
          [])))))


(defn states-syms-att
  "Input: len-4 vect or from AT&T line; output: vector of keywords (states) and
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
        {:delta-key [:delta st-i sym-i st-o]
         :delta-val sym-o
         :sigma [sym-i sym-o]})
      {:F [(keyword (str "s" (first fields)))]})))


(defn add-att-line-to-fst
  "Return a new `fst` hash built by updating the passed-in one with the AT&T
  line"
  [fst line]
  (let [p-l (process-line-att line)]
    (assoc
      (assoc
        (assoc-in
          fst
          (get p-l :delta-key [:delta])
          (get p-l :delta-val (:delta fst)))
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
       :delta {}  ;; maps st-i -> sym-i -> st-o -> sym-o
      }
      (line-seq rdr))))


(def regex-stmt
  (insta/parser (clojure.java.io/resource "grammar.bnf")))


(defn -main
  "Provide an AT&T-formatted FST path and an input string and behold the
  apply-down-ness!"
  [& args]
  (clojure.pprint/pprint (regex-stmt (first args)))
  ;; (println (apply-down (parse-att (first args)) (second args)))
)
