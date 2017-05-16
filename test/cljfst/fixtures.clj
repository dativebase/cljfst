(ns cljfst.fixtures
  (:require [clojure.pprint :refer [pprint]]
            [cljfst.common :refer [unknown-symbol
                                   identity-symbol
                                   epsilon-symbol]]))

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

;; non-determinized "a:b c:d ;"
(def non-determinized-concat-fst
  {:sigma #{"d" "a" "b" "c"},
   :Q #{:s0 :s1 :s3 :s2},
   :s0 :s0,
   :F #{:s3},
   :delta #{[:s2 "c" :s3 "d"] [:s1 "@0@" :s2 "@0@"] [:s0 "a" :s1 "b"]}})

