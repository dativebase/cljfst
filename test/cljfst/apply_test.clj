(ns cljfst.apply-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [cljfst.fixtures :refer :all]
            [cljfst.apply :refer :all]
            [cljfst.common :refer [unknown-symbol
                                   identity-symbol
                                   epsilon-symbol]]
            [cljfst.minimize :refer [minimize-hcc
                                     hopcroft-canonical-equiv-classes
                                     hopcroft-optimized-equiv-classes]]
            [cljfst.determinize :refer [determinize
                                        E
                                        subset-construction]]))

(deftest test-apply-down
  (testing "apply-down on test-fst-1 with input \"a\""
    (is (= "b" (first (apply-down test-fst-1 "a"))))))
