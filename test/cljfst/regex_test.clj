(ns cljfst.regex-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [cljfst.regex :refer :all]
            [cljfst.determinize :refer [subset-construction]]
            [cljfst.apply :refer [apply-down]]
            [cljfst.iface :refer [parse-att
                                  print-net]]
            [cljfst.fixtures :refer :all]
            [cljfst.common :refer [unknown-symbol
                                   identity-symbol
                                   epsilon-symbol]]))

;; regex a:b ;
;; Sigma: a b
;; Ss0:<a:b> -> fs1.
;; fs1:(no arcs).
(deftest test-fst-atomic
  (testing "\"regex a:b ;\" produces the correct fst"
    (let [regex-cmd "a:b ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{"a" "b"} (set (:sigma fst))))
      (is (= #{[:s0 "a" :s1 "b"]} (set (:delta fst))))
      (is (= :s0 (:s0 fst)))
      (is (= #{:s1} (:F fst))))))

;; regex a:? ;
;; Sigma: ? @ a
;; Ss0: <a:?> -> fs1, a -> fs1.
(deftest test-fst-sym-unknown
  (testing "\"regex a:? ;\" produces the correct fst"
    (let [regex-cmd "a:? ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{unknown-symbol identity-symbol "a"}
             (set (:sigma fst))))
      (is (= #{[:s0 "a" :s1 unknown-symbol]
               [:s0 "a" :s1 "a"]} (set (:delta fst))))
      (is (= :s0 (:s0 fst)))
      (is (= #{:s1} (:F fst))))))

;; regex ?:a ;
;; Sigma: ? @ a
;; Ss0: <?:a> -> fs1, a -> fs1.
(deftest test-fst-unknown-sym
  (testing "\"regex ?:a ;\" produces the correct fst"
    (let [regex-cmd "?:a ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{"@_UNKNOWN_SYMBOL_@" "@_IDENTITY_SYMBOL_@" "a"}
             (set (:sigma fst))))
      (is (= #{[:s0 "@_UNKNOWN_SYMBOL_@" :s1 "a"]
               [:s0 "a" :s1 "a"]} (set (:delta fst))))
      (is (= :s0 (:s0 fst)))
      (is (= #{:s1} (:F fst))))))

;; regex a:a ;
;; Sigma: a
;; Ss0:a -> fs1.
(deftest test-fst-sym-sym
  (testing "\"regex a:a ;\" produces the correct fst"
    (let [regex-cmd "a:a ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{"a"} (set (:sigma fst))))
      (is (= #{[:s0 "a" :s1 "a"]} (:delta fst)))
      (is (= :s0 (:s0 fst)))
      (is (= #{:s1} (:F fst))))))

;; regex a ;
;; Sigma: a
;; Ss0:a -> fs1.
(deftest test-fst-sym
  (testing "\"regex a ;\" produces the correct fst"
    (let [regex-cmd "a ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{"a"} (set (:sigma fst))))
      (is (= #{[:s0 "a" :s1 "a"]} (:delta fst)))
      (is (= :s0 (:s0 fst)))
      (is (= #{:s1} (:F fst))))))

;; regex a|b ;
;; Sigma: a b
;; Ss0:a -> fs1, b -> fs1.
(deftest test-fst-union
  (testing "\"regex a|b ;\" produces the correct fst"
    (let [regex-cmd "a|b ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{"a" "b"} (set (:sigma fst))))
      ;; Note: the following tests on the FST will fail because my FST compiler
      ;; does not yet minimize...
      ;; (is (= #{[:s0 "a" :s1 "a"]
      ;;          [:s0 "b" :s1 "b"]} (set (:delta fst))))
      ;; (is (= :s0 (:s0 fst)))
      ;; (is (= [:s1] (:F fst)))
      (is (= "b" (first (apply-down fst "b"))))
      (is (= "a" (first (apply-down fst "a"))))
      (is (empty? (apply-down fst "c"))))))

;; regex a b ;
;; Sigma: a b
;; Ss0: a -> s1
;; s1:b -> fs2
(deftest test-fst-concat
  (testing "\"regex a b ;\" produces the correct fst"
    (let [regex-cmd "a b ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      ;; (pprint parse)
      ;; (pprint fst)
      (is (= #{"a" "b"} (set (:sigma fst))))
      ;; Note: the following tests on the FST will fail because my FST compiler
      ;; does not yet minimize...
      ;; (is (= #{[:s0 "a" :s1 "a"]
      ;;          [:s1 "b" :s2 "b"]} (set (:delta fst))))
      ;; (is (= [:s2] (:F fst)))
      (is (= :s0 (:s0 fst)))
      (is (= "ab" (first (apply-down fst "ab"))))
      (is (empty? (apply-down fst "aba"))))))

(deftest test-merge-alphabet
  (testing "`merge-alphabet` works as expected"
    (let [[merged-alpha-1 merged-alpha-2]
          (merge-alphabets fst-for-merge-1 fst-for-merge-2)]
      (is (some #{[:s0 "c" :s0 "c"]} (:delta merged-alpha-1)))
      (is (some #{[:s0 "a" :s0 "a"]} (:delta merged-alpha-2)))
      (is (some #{[:s0 "b" :s0 "b"]} (:delta merged-alpha-2))))
    (let [[merged-alpha-1 merged-alpha-3]
          (merge-alphabets fst-for-merge-1 fst-for-merge-3)]
      (is (some #{[:s0 "d" :s0 "d"]} (:delta merged-alpha-1)))
      (is (some #{[:s0 "a" :s0 "d"]} (:delta merged-alpha-3)))
      (is (some #{[:s0 "b" :s0 "d"]} (:delta merged-alpha-3))))))

(deftest test-state-pair-converter
  (testing "get-state-pair-converter returns a function that converts pairs of
           states to state keywords."
    (let [converter (get-state-pair-converter [:s0 :s0])]
      (is (= :s0 (converter [:s0 :s0])))
      (is (= :s1 (converter [:s0 :sink])))
      (is (= :s2 (converter [:sink :sink])))
      (is (= :s3 (converter [:sink :s0])))
      (is (= :s4 (converter [:s2 :s1])))
      (is (= :s5 (converter [:s1 :s2])))
      (is (= :s1 (converter [:s0 :sink]))))))

(deftest test-fst-union-product-construction
  (testing "FST union via ProductConstruction algorithm"
    (let [fst1 (parse-to-fst (read-regex "a ;"))
          fst2 (parse-to-fst (read-regex "b ;"))
          un (union-pc fst1 fst2)]
      (is (= "a" (first (apply-down un "a"))))
      (is (= "a" (first (apply-down fst1 "a"))))
      (is (= nil (first (apply-down fst2 "a"))))
      (is (= "b" (first (apply-down un "b"))))
      (is (= nil (first (apply-down fst1 "b"))))
      (is (= "b" (first (apply-down fst2 "b")))))
    (let [fst1 (parse-to-fst (read-regex "a:b ;"))
          fst2 (parse-to-fst (read-regex "c:d ;"))
          un (union-pc fst1 fst2)]
      ;; (pprint fst1)
      ;; (pprint fst2)
      ;; (pprint un)
      (is (= "b" (first (apply-down un "a"))))
      (is (= "b" (first (apply-down fst1 "a"))))
      (is (= nil (first (apply-down fst2 "a"))))
      (is (= "d" (first (apply-down un "c"))))
      (is (= nil (first (apply-down fst1 "c"))))
      (is (= "d" (first (apply-down fst2 "c")))))))

(deftest test-fst-intersection-product-construction
  (testing "FST intersection via ProductConstruction algorithm"
    (let [fst1 (parse-to-fst (read-regex "a|b ;"))
          fst1 (subset-construction fst1)
          fst2 (parse-to-fst (read-regex "a ;"))
          fst2 (subset-construction fst2)
          in (intersection-pc fst1 fst2)]
      (is (= "a" (first (apply-down in "a"))))
      (is (= "a" (first (apply-down fst1 "a"))))
      (is (= "a" (first (apply-down fst2 "a"))))
      (is (= nil (first (apply-down in "b"))))
      (is (= "b" (first (apply-down fst1 "b"))))
      (is (= nil (first (apply-down fst2 "b")))))
    (let [fst1 (subset-construction (parse-to-fst (read-regex "a:b ;")))
          fst2 (subset-construction (parse-to-fst (read-regex "c:d ;")))
          in (intersection-pc fst1 fst2)]
      (is (= nil (first (apply-down in "a"))))
      (is (= "b" (first (apply-down fst1 "a"))))
      (is (= nil (first (apply-down fst2 "a"))))
      (is (= nil (first (apply-down in "c"))))
      (is (= nil (first (apply-down fst1 "c"))))
      (is (= "d" (first (apply-down fst2 "c")))))))

(deftest test-fst-subtraction-product-construction
  (testing "FST subtraction via ProductConstruction algorithm"
    (let [fst1 (parse-to-fst (read-regex "a|b ;"))
          fst1 (subset-construction fst1)
          fst2 (parse-to-fst (read-regex "a ;"))
          fst2 (subset-construction fst2)
          sub (subtraction-pc fst1 fst2)]
      (is (= nil (first (apply-down sub "a"))))
      (is (= "a" (first (apply-down fst1 "a"))))
      (is (= "a" (first (apply-down fst2 "a"))))
      (is (= "b" (first (apply-down sub "b"))))
      (is (= "b" (first (apply-down fst1 "b"))))
      (is (= nil (first (apply-down fst2 "b")))))
    (let [fst1 (subset-construction (parse-to-fst (read-regex "a:b ;")))
          fst2 (subset-construction (parse-to-fst (read-regex "c:d ;")))
          sub (subtraction-pc fst1 fst2)]
      (is (= "b" (first (apply-down sub "a"))))
      (is (= "b" (first (apply-down fst1 "a"))))
      (is (= nil (first (apply-down fst2 "a"))))
      (is (= nil (first (apply-down sub "c"))))
      (is (= nil (first (apply-down fst1 "c"))))
      (is (= "d" (first (apply-down fst2 "c")))))))

(deftest test-complex-regex
  (testing "Complex regexes are parsed and interpreted"
    (let [parse (read-regex "[a:b|c:d]* | x ;")
          fst (parse-to-fst parse)]
      ;; (println "complex regex")
      ;; (pprint parse)
      ;; (pprint fst)
      (is (= "bdb" (first (apply-down fst "aca")))))
    (let [parse (read-regex "a:b|c* ;")
          fst (parse-to-fst parse)]
      ;; (println "complex regex")
      ;; (pprint parse)
      ;; (pprint fst)
      (is (= "b" (first (apply-down fst "a"))))
      (is (= "ccc" (first (apply-down fst "ccc")))))))

(deftest test-parse-reserved-symbols
  (testing "Reserved symbol escaping in regexes works"
    (let [regex "a|%||b ;"
          parse (read-regex regex)
          fst (parse-to-fst parse)]
      ;; (pprint parse)
      ;; (pprint fst)
      (is (= "a" (first (apply-down fst "a"))))
      (is (= "b" (first (apply-down fst "b"))))
      (is (= "|" (first (apply-down fst "|"))))
      (is (= nil (first (apply-down fst "c")))))
    (let [regex "a|\"|\"|b ;"
          parse (read-regex regex)
          fst (parse-to-fst parse)]
      ;; (pprint parse)
      ;; (pprint fst)
      (is (= "a" (first (apply-down fst "a"))))
      (is (= "b" (first (apply-down fst "b"))))
      (is (= "|" (first (apply-down fst "|"))))
      (is (= nil (first (apply-down fst "c")))))))

(deftest test-multi-char-symbols
  (testing "Multi-character symbols in regexes work"
    (let [regex "a%|b ;"
          parse (read-regex regex)
          fst (parse-to-fst parse)]
      ;; (pprint parse)
      ;; (pprint fst)
      (is (= nil (first (apply-down fst "a"))))
      (is (= nil (first (apply-down fst "b"))))
      (is (= nil (first (apply-down fst "|"))))
      (is (= "a|b" (first (apply-down fst "a|b")))))
    (let [regex "\"a|b\" ;"
          parse (read-regex regex)
          fst (parse-to-fst parse)]
      ;; (pprint parse)
      ;; (pprint fst)
      (is (= nil (first (apply-down fst "a"))))
      (is (= nil (first (apply-down fst "b"))))
      (is (= nil (first (apply-down fst "|"))))
      (is (= "a|b" (first (apply-down fst "a|b")))))))

;; regex a* ;
;; Sigma: a
;; Sfs0: a -> fs0
(deftest test-fst-kleene-atomic
  (testing "\"regex a*;\" produces the correct fst"
    (let [regex-cmd "a* ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{"a" epsilon-symbol} (:sigma fst)))
      (is (= "a" (first (apply-down fst "a"))))
      (is (= "aaaa" (first (apply-down fst "aaaa"))))
      (is (= "" (first (apply-down fst ""))))
      (is (empty? (apply-down fst "ab"))))))

;; The test-att-1 file encodes the regex a -> b || c _ d ;
;; When reversed, it should behave like a -> b || d _ c ;
(deftest test-reverse-fst
  (testing "`referse-fst` works as expected"
    (let [fst (parse-att "resources/test-att-1")
          fst-rev (reverse-fst fst)]
      (is (= "cbd" (first (apply-down fst "cad"))))
      (is (= "dac" (first (apply-down fst "dac"))))
      (is (= "cad" (first (apply-down fst-rev "cad"))))
      (is (= "dbc" (first (apply-down fst-rev "dac")))))))

(deftest test-Sigma-Sigma
  (testing "The FST mapping any symbol to any other, including itself, i.e.,
           (Sigma:Sigma)."
    (let [fst Sigma-Sigma]
      (is (some #{"cad"} (apply-down fst "cad")))
      (is (some #{"???"} (apply-down fst "cad")))
      (is (some #{"c?d"} (apply-down fst "cad"))))))

(deftest test-Sigma-epsilon
  (testing "The FST mapping any symbol to the empty string, i.e.,
           (Sigma:epsilon)."
    (let [fst Sigma-epsilon]
      ;; (pprint (apply-down fst "cad"))
      (is (= "" (first (apply-down fst "cad"))))
      (is (= "" (first (apply-down fst ""))))
      (is (= "" (first (apply-down fst "monkey bark")))))))

(deftest test-epsilon-Sigma
  (testing "The FST mapping the empty string to any symbol, i.e.,
           (epsilon:Sigma)."
    (let [fst epsilon-Sigma]
      ;; (pprint fst)
      ;; WARNING: apply-down on this FST will cause a StackOverflowError.
      ;; (pprint (apply-down fst ""))
      ;; (pprint (apply-down fst "cad"))
      ;; (is (= "" (first (apply-down fst "cad"))))
      ;; (is (= "" (first (apply-down fst ""))))
      ;; (is (= "" (first (apply-down fst "monkey bark"))))
      )))

(deftest test-is-cyclic
  (testing "If we can correctly identify cyclic FSTs."
    (let [fst epsilon-Sigma]
      (is (= true (is-cyclic fst))))
    (let [regex-cmd "a* ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= true (is-cyclic fst))))
    (let [regex-cmd "a|b ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= false (is-cyclic fst))))
    (let [regex-cmd "a:b c:d ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= false (is-cyclic fst))))))

;; WARNING: more tests on `count-paths` are needed, with more complex acyclic
;; FSTs.
(deftest test-count-paths
  (testing "If we can correctly count paths in acyclic FSTs."
    (let [regex-cmd "[a:b c:d] | [a:x c:x] | [a:y c:y] ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= false (is-cyclic fst)))
      (is (= 3 (count-paths fst))))))

(deftest test-path-complement
  (testing "If `path-complement` behaves correctly"
    (let [regex-cmd "[a:b c:d] ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      ;; (pprint parse)
      ;; (pprint fst)
      ;; (println "apply-down 'ac' with '[a:b c:d]'")
      ;; (println (apply-down fst "ac"))
      (is (= "bd" (first (apply-down fst "ac")))))
    (let [regex-cmd "~[a:b c:d] ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      ;; (pprint parse)
      ;; (pprint fst)
      ;; (print-net fst)
      ;; (println "apply-down 'ac' with '~[a:b c:d]'")
      ;; (println (apply-down fst "ac"))
      ;; WARNING: foma returns "???" for "down ac" with the above FST. That
      ;; seems like the complement of the FSA "ac", not the path complement of
      ;; the FST [a:b c:d]
      (is (= nil (some #{"bd"} (apply-down fst "ac")))))))

(deftest test-fst->fsa
  (testing "We can get an FSA from an FST."
    (let [regex-cmd "a:b c:d ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)
          fsa (fst->fsa fst)
          fsa-low (fst->fsa fst :lower)]
      (is (= "bd" (first (apply-down fst "ac"))))
      (is (= nil (first (apply-down fst "bd"))))
      (is (= "ac" (first (apply-down fsa "ac"))))
      (is (= nil (first (apply-down fsa "bd"))))
      (is (= "bd" (first (apply-down fsa-low "bd"))))
      (is (= nil (first (apply-down fsa-low "ac")))))))

(deftest test-cross-product
  (testing "Cross-product can take two FSTs/FSAs and return a new FST."
    (let [regex-cmd "a|b ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)
          fsa1 (fst->fsa fst)
          regex-cmd "x|y ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)
          fsa2 (fst->fsa fst)
          fst (cross-product fsa1 fsa2)]
      (println "FSA1")
      (pprint fsa1)
      (println "FSA2")
      (pprint fsa2)
      (pprint fst)
      )))

