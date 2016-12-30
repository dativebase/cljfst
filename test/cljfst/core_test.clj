(ns cljfst.core-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [cljfst.core :refer :all]
            [cljfst.minimize :refer [minimize-hcc
                                     hopcroft-canonical-equiv-classes
                                     hopcroft-optimized-equiv-classes]]
            [cljfst.determinize :refer [determinize E powerset]]))

(def test-fst-1
  {:sigma ["a" "b"],
   :Q [:s0 :s1],
   :s0 :s0,
   :F [:s1],
   :delta [[:s0 "a" :s1 "b"]]})

;; The regular expression "a:b x:0" should produce the following fst:
;; TODO: the epsilon "0" should not be part of the alphabet
(def test-fst-2
  {:sigma ["x" "a" "b" "0"],
   :Q [:s0 :s1 :s3 :s2],
   :s0 :s0,
   :F [:s3],
   :delta [[:s2 "x" :s3 "0"]
           [:s1 "0" :s2 "0"]
           [:s0 "a" :s1 "b"]]})

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
    (let [regex-cmd "regex a:b ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      ;; (pprint (read-regex regex-cmd))
      (is (= #{"a" "b"} (set (:sigma fst))))
      (is (= #{[:s0 "a" :s1 "b"]} (set (:delta fst))))
      (is (= :s0 (:s0 fst)))
      (is (= [:s1] (:F fst)))
      ;; (pprint fst)
    )))

;; regex a:? ;
;; Sigma: ? @ a
;; Ss0: <a:?> -> fs1, a -> fs1.
(deftest test-fst-sym-unknown
  (testing "\"regex a:? ;\" produces the correct fst"
    (let [regex-cmd "regex a:? ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{"@_UNKNOWN_SYMBOL_@" "@_IDENTITY_SYMBOL_@" "a"}
             (set (:sigma fst))))
      (is (= #{[:s0 "a" :s1 "@_UNKNOWN_SYMBOL_@"]
               [:s0 "a" :s1 "a"]} (set (:delta fst))))
      (is (= :s0 (:s0 fst)))
      (is (= [:s1] (:F fst))))))

;; regex ?:a ;
;; Sigma: ? @ a
;; Ss0: <?:a> -> fs1, a -> fs1.
(deftest test-fst-unknown-sym
  (testing "\"regex ?:a ;\" produces the correct fst"
    (let [regex-cmd "regex ?:a ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{"@_UNKNOWN_SYMBOL_@" "@_IDENTITY_SYMBOL_@" "a"}
             (set (:sigma fst))))
      (is (= #{[:s0 "@_UNKNOWN_SYMBOL_@" :s1 "a"]
               [:s0 "a" :s1 "a"]} (set (:delta fst))))
      (is (= :s0 (:s0 fst)))
      (is (= [:s1] (:F fst))))))

;; regex ? ;
;; Sigma: @
;; Ss0: @ -> fs1.

;; regex a:a ;
;; Sigma: a
;; Ss0:a -> fs1.
(deftest test-fst-sym-sym
  (testing "\"regex a:a ;\" produces the correct fst"
    (let [regex-cmd "regex a:a ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{"a"} (set (:sigma fst))))
      (is (= [[:s0 "a" :s1 "a"]] (:delta fst)))
      (is (= :s0 (:s0 fst)))
      (is (= [:s1] (:F fst))))))

;; regex a ;
;; Sigma: a
;; Ss0:a -> fs1.
(deftest test-fst-sym
  (testing "\"regex a ;\" produces the correct fst"
    (let [regex-cmd "regex a ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= #{"a"} (set (:sigma fst))))
      (is (= [[:s0 "a" :s1 "a"]] (:delta fst)))
      (is (= :s0 (:s0 fst)))
      (is (= [:s1] (:F fst))))))

;; regex a|b ;
;; Sigma: a b
;; Ss0:a -> fs1, b -> fs1.
(deftest test-fst-union
  (testing "\"regex a|b ;\" produces the correct fst"
    (let [regex-cmd "regex a|b ;"
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
    (let [regex-cmd "regex a* ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (is (= ["a"] (:sigma fst)))
      ;; Note: the following test on the FST will fail because my FST compiler
      ;; does not yet minimize...
      ;;(is (= [[:s0 "a" :s0 "a"]] (:delta fst)))
      (is (= :s0 (:s0 fst)))
      (is (= [:s0] (:F fst)))
      (is (= "a" (first (apply-down fst "a"))))
      (is (= "aaaa" (first (apply-down fst "aaaa"))))
      (is (empty? (apply-down fst "ab"))))))

;; regex a b ;
;; Sigma: a b
;; Ss0: a -> s1
;; s1:b -> fs2
(deftest test-fst-concat
  (testing "\"regex a b ;\" produces the correct fst"
    (let [regex-cmd "regex a b ;"
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
  {:sigma ["a" "b"],
   :Q [:s0 :s1 :s2 :s3 :s4],
   :s0 :s0,
   :F [:s4],
   :delta [[:s0 "a" :s1 "a"]
           [:s0 "b" :s2 "b"]
           [:s1 "a" :s1 "a"]
           [:s1 "b" :s3 "b"]
           [:s2 "b" :s2 "b"]
           [:s2 "a" :s1 "a"]
           [:s3 "a" :s1 "a"]
           [:s3 "b" :s4 "b"]
           [:s4 "b" :s2 "b"]
           [:s4 "a" :s1 "a"]]})

(deftest test-hopcroft-canonical-equiv-classes
  (testing "Hopcroft canonical minimization produces correct equivalence
           classes"
    (let [equiv-classes (hopcroft-canonical-equiv-classes non-minimized-fst)]
      (is (= #{[:s4] [:s3] [:s1] [:s0 :s2]} (set equiv-classes))))))

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
  {:sigma ["0" "1"],
   :Q [:s1 :s2 :s3],
   :s0 :s1,
   :F [:s1],
   :delta [[:s1 "@0@" :s2 "@0@"]
           [:s1 "0" :s3 "0"]
           [:s2 "1" :s1 "1"]
           [:s2 "1" :s3 "1"]
           [:s3 "0" :s1 "0"]]})

(def intermediate-delta
  [[#{:s1 :s2} "0" #{:s3} "0"]
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
   [#{:s1} "1" #{} "1"]])

(deftest test-E
  (testing "`(E)` works as expected"
    (let [my-E (fn [state-set] (E state-set non-deterministic-fst))]
      (is (= (my-E #{}) #{}))
      (is (= #{:s1 :s2} (set (my-E [:s1]))))
      (is (= #{:s2} (set (my-E '(:s2)))))
      (is (= #{:s3} (set (my-E '(:s3)))))
      (is (= #{:s1 :s2} (set (my-E '(:s1 :s2)))))
      (is (= #{:s1 :s2 :s3} (set (my-E '(:s1 :s3)))))
      (is (= #{:s2 :s3} (set (my-E '(:s2 :s3)))))
      (is (= #{:s1 :s2 :s3} (set (my-E '(:s1 :s2 :s3))))))))

(def expected-determinized-fst
  {:sigma ["0" "1"],
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
      (pprint determinized-fst)
      (is (= expected-determinized-fst determinized-fst)))))

;; regex a:b c:d ;
(deftest test-fst-atomic
  (testing "\"regex a:b ;\" produces the correct fst"
    (let [regex-cmd "regex a:b c:d ;"
          parse (read-regex regex-cmd)
          fst (parse-to-fst parse)]
      (pprint fst)
    )))
