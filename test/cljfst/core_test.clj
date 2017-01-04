(ns cljfst.core-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [cljfst.core :refer :all]
            [cljfst.common :refer [powerset
                                   unknown-symbol
                                   identity-symbol
                                   epsilon-symbol]]
            [cljfst.minimize :refer [minimize-hcc
                                     hopcroft-canonical-equiv-classes
                                     hopcroft-optimized-equiv-classes]]
            [cljfst.determinize :refer [determinize
                                        E
                                        subset-construction]]))

(def test-fst
  {:sigma #{"a" "b" "c" "d"}   ;; alphabet
   :Q #{:s0 :s1 :s2 :s3}       ;; all states
   :s0 :s0                     ;; initial state
   :F #{:s0 :s1 :s2}           ;; final states
   :delta #{[:s0 "@" :s0 "@"]  ;; transition matrix: read 1 in 0, write 3, move
            [:s0 "a" :s0 "a"]  ;; to 2
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
            [:s3 "d" :s0 "d"]}})

(def test-fst-1
  {:sigma #{"a" "b"},
   :Q #{:s0 :s1},
   :s0 :s0,
   :F #{:s1},
   :delta #{[:s0 "a" :s1 "b"]}})

;; The regular expression "a:b x:0" should produce the following fst:
;; TODO: the epsilon "0" should not be part of the alphabet
(def test-fst-2
  {:sigma #{"x" "a" "b" "0"},
   :Q #{:s0 :s1 :s3 :s2},
   :s0 :s0,
   :F #{:s3},
   :delta #{[:s2 "x" :s3 "0"]
            [:s1 "0" :s2 "0"]
            [:s0 "a" :s1 "b"]}})

(deftest test-apply-down
  (testing "apply-down on test-fst-1 with input \"a\""
    (is (= "b" (first (apply-down test-fst-1 "a"))))))

;;(deftest test-merge-alphabets
;;  (testing "merge-alphabets correctly merges the alphabets of two fsts"
;;    (println (merge-alphabets test-fst-1 test-fst-2))))

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
      (is (= #{"@_UNKNOWN_SYMBOL_@" "@_IDENTITY_SYMBOL_@" "a"}
             (set (:sigma fst))))
      (is (= #{[:s0 "a" :s1 "@_UNKNOWN_SYMBOL_@"]
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

;; regex ? ;
;; Sigma: @
;; Ss0: @ -> fs1.

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

;; regex a* ;
;; Sigma: a
;; Sfs0: a -> fs0
(deftest test-fst-kleene-atomic
  (testing "\"regex a*;\" produces the correct fst"
    (let [regex-cmd "a* ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{"a" epsilon-symbol} (:sigma fst)))
      ;; Note: the following test on the FST will fail because my FST compiler
      ;; does not yet minimize...
      ;;(is (= [[:s0 "a" :s0 "a"]] (:delta fst)))
      (is (= :s0 (:s0 fst)))
      (is (= #{:s0} (:F fst)))
      (is (= "a" (first (apply-down fst "a"))))
      (is (= "aaaa" (first (apply-down fst "aaaa"))))
      (is (= "" (first (apply-down fst ""))))
      (is (empty? (apply-down fst "ab"))))))

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

;; From Hulden p. 82
(def non-minimized-fst
  {:sigma #{"a" "b"},
   :Q #{:s0 :s1 :s2 :s3 :s4},
   :s0 :s0,
   :F #{:s4},
   :delta #{[:s0 "a" :s1 "a"]
            [:s0 "b" :s2 "b"]
            [:s1 "a" :s1 "a"]
            [:s1 "b" :s3 "b"]
            [:s2 "b" :s2 "b"]
            [:s2 "a" :s1 "a"]
            [:s3 "a" :s1 "a"]
            [:s3 "b" :s4 "b"]
            [:s4 "b" :s2 "b"]
            [:s4 "a" :s1 "a"]}})

(deftest test-hopcroft-canonical-equiv-classes
  (testing "Hopcroft canonical minimization produces correct equivalence
           classes"
    (let [equiv-classes (hopcroft-canonical-equiv-classes non-minimized-fst)]
      (is (= #{#{:s4} #{:s3} #{:s1} #{:s0 :s2}} (set equiv-classes))))))

;; When minimized, all instances of :s2 in `non-minimized-fst` should be
;; replaced with :s0
(deftest test-hopcroft-canonical-minimization
  (testing "Hopcroft canonical minimization algorithm works"
    (let [minimized-fst (minimize-hcc non-minimized-fst)
          expected-delta (set [
                              [:s0 "a" :s1 "a"]
                              [:s0 "b" :s0 "b"]
                              [:s1 "a" :s1 "a"]
                              [:s1 "b" :s3 "b"]
                              [:s3 "a" :s1 "a"]
                              [:s3 "b" :s4 "b"]
                              [:s4 "b" :s0 "b"]
                              [:s4 "a" :s1 "a"]])]
      (is (= #{:s0 :s1 :s3 :s4} (set (:Q minimized-fst))))
      (is (= [:s4] (:F minimized-fst)))
      (is (= expected-delta (set (:delta minimized-fst)))))))


;; NFA (from Dave Bacon UW slides)
(def non-deterministic-fst
  {:sigma #{"0" "1"},
   :Q #{:s1 :s2 :s3},
   :s0 :s1,
   :F #{:s1},
   :delta #{[:s1 "@0@" :s2 "@0@"]
            [:s1 "0" :s3 "0"]
            [:s2 "1" :s1 "1"]
            [:s2 "1" :s3 "1"]
            [:s3 "0" :s1 "0"]}})

(def intermediate-delta
  #{[#{:s1 :s2} "0" #{:s3} "0"]
    [#{:s1 :s2} "1" #{:s1 :s3} "1"]
    [#{} "0" #{} "0"]
    [#{} "1" #{} "1"]
    [#{:s2} "0" #{} "0"]
    [#{:s2} "1" #{:s1 :s3} "1"]
    [#{:s3} "0" #{:s1} "0"]
    [#{:s3} "1" #{} "1"]
    [#{:s3 :s2} "0" #{:s1} "0"]
    [#{:s3 :s2} "1" #{:s1 :s3} "1"]
    [#{:s1 :s3} "0" #{:s1 :s3} "0"]
    [#{:s1 :s3} "1" #{} "1"]
    [#{:s1 :s3 :s2} "0" #{:s1 :s3} "0"]
    [#{:s1 :s3 :s2} "1" #{:s1 :s3} "1"]
    [#{:s1} "0" #{:s3} "0"]
    [#{:s1} "1" #{} "1"]})

(deftest test-E
  (testing "`(E)` works as expected"
    (let [my-E (fn [state-set] (E state-set non-deterministic-fst))]
      (is (= (my-E #{}) #{}))
      (is (= #{:s1 :s2} (set (my-E #{:s1}))))
      (is (= #{:s2} (set (my-E #{:s2}))))
      (is (= #{:s3} (set (my-E #{:s3}))))
      (is (= #{:s1 :s2} (set (my-E #{:s1 :s2}))))
      (is (= #{:s1 :s2 :s3} (set (my-E #{:s1 :s3}))))
      (is (= #{:s2 :s3} (set (my-E #{:s2 :s3}))))
      (is (= #{:s1 :s2 :s3} (set (my-E #{:s1 :s2 :s3})))))))

(def expected-determinized-fst
  {:sigma #{"0" "1"},
   :Q #{:s0 :s1 :s3 :s2},
   :s0 :s0,
   :F #{:s0 :s3},
   :delta #{[:s0 "0" :s2 "0"]
            [:s0 "1" :s3 "1"]
            [:s1 "0" :s1 "0"]
            [:s1 "1" :s1 "1"]
            [:s2 "0" :s0 "0"]
            [:s2 "1" :s1 "1"]
            [:s3 "0" :s3 "0"]
            [:s3 "1" :s3 "1"]}})

(deftest test-determinize
  (testing "`(determinize non-deterministic-fst)` works"
    (let [determinized-fst (determinize non-deterministic-fst)
          det-delta (:delta determinized-fst)]
      ;;(println "determinize:")
      ;;(pprint determinized-fst)
      ;;(println "\n")
      (is (= expected-determinized-fst determinized-fst)))))

;; a -> b ;
(def fst-for-merge-1
  {:sigma #{unknown-symbol identity-symbol "a" "b"}
   :Q #{:s0}
   :s0 :s0
   :F #{:s0}
   :delta #{[:s0 identity-symbol :s0 identity-symbol]
            [:s0 "b" :s0 "b"]
            [:s0 "a" :s0 "b"]}})

;; c -> 0 ;
(def fst-for-merge-2
  {:sigma #{unknown-symbol identity-symbol "c"}
   :Q #{:s0}
   :s0 :s0
   :F #{:s0}
   :delta #{[:s0 identity-symbol :s0 identity-symbol]
            [:s0 "c" :s0 epsilon-symbol]}})

;; ? -> d ;
(def fst-for-merge-3
  {:sigma #{unknown-symbol identity-symbol "d"}
   :Q #{:s0}
   :s0 :s0
   :F #{:s0}
   :delta #{[:s0 unknown-symbol :s0 "d"]
            [:s0 "d" :s0 "d"]}})

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

(deftest test-subset-construction
  (testing "SubsetConstruction as determinization works"
    (let [regex-cmd "a:b c:d ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)
          determinized-fst (subset-construction fst)]
      (is (= "bd" (first (apply-down fst "ac"))))
      (is (= "bd" (first (apply-down determinized-fst "ac"))))
      (is (= nil (first (apply-down fst "a"))))
      (is (= nil (first (apply-down determinized-fst "a"))))
      (is (not (empty? (filter
                         (fn [[st-i sy-i st-o sy-o]]
                           (and (= sy-i epsilon-symbol)
                                (= sy-o epsilon-symbol)))
                         (:delta fst)))))
      (is (empty? (filter
                    (fn [[st-i sy-i st-o sy-o]]
                      (and (= sy-i epsilon-symbol)
                           (= sy-o epsilon-symbol)))
                    (:delta determinized-fst)))))
    (let [determinized-fst (subset-construction non-deterministic-fst)
          det-delta (:delta determinized-fst)])))

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
      ;; Note: the following test on the FST will fail because my FST compiler
      ;; does not yet minimize...
      ;;(is (= [[:s0 "a" :s0 "a"]] (:delta fst)))
      (pprint fst)
      (is (= "a" (first (apply-down fst "a"))))
      (is (= "aaaa" (first (apply-down fst "aaaa"))))
      (is (empty? (apply-down fst "ab")))
      (println "fst for a*:")
      (pprint fst)
      (let [det-fst (subset-construction fst)]
        (println "\ndeterminized fst for a*:")
        (pprint det-fst))
      )))


