(ns cljfst.regex-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [cljfst.regex :refer :all]
            [cljfst.determinize :refer [subset-construction]]
            [cljfst.apply :refer [apply-down]]
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
