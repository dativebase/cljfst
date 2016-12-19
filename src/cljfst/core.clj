(ns cljfst.core
  (:gen-class))

;; Formally, a finite transducer T is a 6-tuple (Q, Σ, Γ, I, F, δ) such that:

;; Q is a finite set, the set of states;
;; Σ is a finite set, called the input alphabet;
;; Γ is a finite set, called the output alphabet;
;; I is a subset of Q, the set of initial states;
;; F is a subset of Q, the set of final states; and
;; δ is a subset of Q x (Σ U {e}) x (Γ U {e}) x Q
;; p. 37

;; Sigma: ? @ a b c d
;; Sfs0:@ -> fs0, a -> fs0, b -> fs0, c -> fs1, d -> fs0.
;; fs1:@ -> fs0, a -> fs2, b -> fs0, c -> fs1, d -> fs0, <a:b> -> s3.
;; s3:d -> fs0.
;; fs2:@ -> fs0, a -> fs0, b -> fs0, c -> fs1.

(def fst1 {:sigma ["a" "b" "c" "d"]
           :Q [:s0 :s1 :s2 :s3]
           :s0 :s0
           :F [:s0 :s1 :s2]
           :delta {:s0 {"@" {:s0 "@"}
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
                   :s3 {"d" {:s0 "d"}}}
           })

;; - default start state: :s0
;; - default start outputs: [""]

;; - input: "cad"
;; - state: :s0
;; - outputs: [""]
;; - get first character "c"
;; - look up [:s0 "c"] in (:delta fst) to get next-state {:s1 "c"}
;; - for each [:state "outchr"] in next-state
;;   - append "outchr" to each string in outputs
;;     [""] -> ["c"]
;;   - return (apply-down fst (rest "cad") :state outputs)
;;     (apply-down fst "ad" :s1 ["c"])

;; - input: "ad"
;; - state: :s1
;; - outputs: ["c"]
;; - get first character "a"
;; - look up [:s1 "a"] in (:delta fst) to get {:s2 "a" :s3 "b"}
;; - for each [:state "outchr"] in next-state
;;   - append "outchr" to each string in outputs
;;     ["c"] -> ["ca"]
;;     ["c"] -> ["cb"]
;;   - return (apply-down fst (rest "ad") :state outputs)
;;     (apply-down fst "d" :s2 ["ca"])
;;     (apply-down fst "d" :s3 ["cb"])

;; - input: "d"
;; - state: :s2
;; - outputs: ["ca"]
;; - get first character "d"
;; - look up [:s2 "d"] in (:delta fst) to get nil
;; - return []

;; - input: "d"
;; - state: :s3
;; - outputs: ["cb"]
;; - get first character "d"
;; - look up [:s3 "d"] in (:delta fst) to get {:s0 "d"}
;; - for each [:state "outchr"] in next-state
;;   - append "outchr" to each string in outputs
;;     ["cb"] -> ["cbd"]
;;   - return (apply-down fst (rest "d") :state outputs)
;;     (apply-down fst "" :s0 ["cbd"])

;; - input: ""
;; - state: :s0
;; - outputs: ["cbd"]
;; - get first character nil
;; - check if :s0 is a final state
;; - it is, so return outputs ["cbd"]

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
                               #(str % next-char)
                               outputs)))
                         next-states))
            []))
        (if (some #{state} (:F fst))
          outputs
          [])))))

(defn -main
  [& args]
  (println (apply-down fst1 (first args))))
