(ns cljfst.common
  (:gen-class))

(defn cart [colls]
  "Return the cartesian product of the collections in `colls`."
  (if (empty? colls)
    '(())
    (for [x (first colls)
          more (cart (rest colls))]
      (cons x more))))

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
