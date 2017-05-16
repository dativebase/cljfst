(ns cljfst.determinize-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [cljfst.determinize :refer :all]
            [cljfst.regex :refer [read-regex
                                  parse-to-fst]]
            [cljfst.apply :refer [apply-down]]
            [cljfst.fixtures :refer :all]
            [cljfst.common :refer [unknown-symbol
                                   identity-symbol
                                   epsilon-symbol]]))

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

(deftest test-determinize
  (testing "`(determinize non-deterministic-fst)` works"
    (let [determinized-fst (determinize non-deterministic-fst)
          det-delta (:delta determinized-fst)]
      ;;(println "determinize:")
      ;;(pprint determinized-fst)
      ;;(println "\n")
      (is (= expected-determinized-fst determinized-fst)))))

(deftest test-subset-construction
  (testing "SubsetConstruction as determinization works"
    (let [fst non-determinized-concat-fst
          determinized-fst (subset-construction fst)]
      (is (= "bd" (first (apply-down fst "ac"))))
      (is (= "bd" (first (apply-down determinized-fst "ac"))))
      (is (= nil (first (apply-down fst "a"))))
      (is (= nil (first (apply-down determinized-fst "a"))))
      (is (= true
             (not (empty? (filter
                         (fn [[st-i sy-i st-o sy-o]]
                           (and (= sy-i epsilon-symbol)
                                (= sy-o epsilon-symbol)))
                         (:delta fst))))))
      (is (empty? (filter
                    (fn [[st-i sy-i st-o sy-o]]
                      (and (= sy-i epsilon-symbol)
                           (= sy-o epsilon-symbol)))
                    (:delta determinized-fst)))))
    (let [determinized-fst (subset-construction non-deterministic-fst)
          det-delta (:delta determinized-fst)])))
