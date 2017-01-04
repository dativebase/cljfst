(ns cljfst.common
  (:gen-class)
  (:require [clojure.set :refer [union]]))

(def epsilon-symbol "@0@")
(def unknown-symbol "@_UNKNOWN_SYMBOL_@")
(def identity-symbol "@_IDENTITY_SYMBOL_@")

(defn cart [colls]
  "Return the cartesian product of the collections in `colls`."
  (if (empty? colls)
    '(())
    (for [x (first colls)
          more (cart (rest colls))]
      (cons x more))))

(defn powerset [ls]
  "Return the powerset of the set `ls`."
  (if (empty? ls) #{#{}}
    (union (powerset (next ls))
           (map #(conj % (first ls)) (powerset (next ls))))))

(defn state-to-int
  "Convert an FST state keyword (like :s1) to an integer (like 1)"
  [state-keyword]
  (Integer. (apply str (nthrest (str state-keyword) 2))))

(defn int-to-state
  "Convert an integer (like 1) to an FST state keyword (like :s1)"
  [state-int]
  (keyword (str "s" state-int)))

(defn inc-state
  "Increment a state (keyword) and return it as a keyword"
  [state-keyword]
  (int-to-state (inc (state-to-int state-keyword))))

(defn pluralize-by-count
  "Pluralize `noun` based on count `count`."
  [noun count]
  (condp = count
    1 noun
    (str noun "s")))

(defn get-next-free-state
  "Get the next free state keyword"
  [state-set]
  (int-to-state (inc (apply max (map state-to-int state-set)))))
