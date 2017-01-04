(ns cljfst.core-test
  (:require [clojure.test :refer :all]
            [clojure.pprint :refer [pprint]]
            [cljfst.core :refer :all]
            [cljfst.common :refer [unknown-symbol
                                   identity-symbol
                                   epsilon-symbol]]))
