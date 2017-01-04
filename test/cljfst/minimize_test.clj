(ns cljfst.minimize-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [cljfst.minimize :refer :all]
            [cljfst.apply :refer [apply-down]]
            [cljfst.fixtures :refer :all]
            [cljfst.common :refer [unknown-symbol
                                   identity-symbol
                                   epsilon-symbol]]))

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
