(ns cljfst.apply
  (:gen-class)
  (:require [clojure.pprint :refer [pprint]]
            [clojure.string :as string]
            [cljfst.common :refer [epsilon-symbol
                                   unknown-symbol
                                   identity-symbol]]))

(defn in-final-with-empty-input
  "Return truthy if we are in a final state with an empty input string."
  [input state fst]
  (and (some #{state} (:F fst))
        (string/blank? input)))

(defn get-transitions
  "Return the transitions that allow the reading of some prefix of string
  `input` when in state `st-i`."
  [fst st-i input sigma]
  (filter
    (fn [[tr-st-i tr-sy-i _ __]]
      (and (= st-i tr-st-i)
           (or (= epsilon-symbol tr-sy-i)
               (= input tr-sy-i)
               (and (= unknown-symbol tr-sy-i) (not (some #{(str (first input))} sigma)))
               (= identity-symbol tr-sy-i)
               (string/starts-with? input tr-sy-i))))
    (:delta fst)))

(defn consume-input
  "Return a 2-ary vector containing a new input string and a new vector of
  output strings by consuming prefix `sy-i` in `input` and suffixing `sy-o` to
  each string in `outputs`."
  [input sy-i sy-o outputs]
  (let [consumed
        (cond
          (= epsilon-symbol sy-i) ""
          (= identity-symbol sy-i) (str (first input))
          (= unknown-symbol sy-i) (str (first input))
          :else sy-i)
        ;; TODO: here you shouldn't be able to read unknown-symbol if (first input) is in alphabet
        ;; debug (println "********************************************************************************")
        ;; debug (println (str "consumed \"" consumed "\""))
        new-input (string/replace-first input consumed "")
        ;; debug (println (str "input changed from \"" input "\" to \"" new-input "\""))
        new-outputs
        (map
          (fn [output]
            ;; (println (str "changing output \"" output "\" to ..."))
            (let [result
                  (cond
                    (= epsilon-symbol sy-o) output
                    (= identity-symbol sy-o) (str output consumed)
                    (= unknown-symbol sy-o) (str output "?")
                    :else (str output sy-o))]
              ;; (println result)
              result
              ))
          outputs)
          ;; debug (println "********************************************************************************")
          ]
    [new-input new-outputs]))

;; TODO: apply-down should first ascertain whether the fst is cyclic. If it is,
;; it should stop recurring after generating a certain threshold of output
;; strings.
(defn apply-down
  "Perform the apply down transformation on string `input` using the FST `fst`"
  ([fst input] (apply-down fst input (:s0 fst) [""]))
  ([fst input state outputs]
   (if (in-final-with-empty-input input state fst)
     (set outputs)
     (let [transitions (get-transitions fst state input (:sigma fst))]
       (set (reduce
         concat
         []
         (map
           (fn [[_ sy-i next-state sy-o]]
             (let [[new-input new-outputs]
                   (consume-input input sy-i sy-o outputs)
                   ;; debug (println (str "in state " state " with outputs " (pr-str outputs) ", reading input " input " and moving to state " next-state " with new input " new-input " and new outputs " (pr-str new-outputs)))
                   ]
               (apply-down fst new-input next-state new-outputs)))
           transitions)))))))
