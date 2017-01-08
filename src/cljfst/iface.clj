;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Clojure FST: Interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This module contains the command-line interface functionality for the
;; Clojure FST CLI. This includes:
;;
;; - AT&T parsing
;; - GraphViz/rhizome.viz FST display (`view net`)
;; - the FST stack
;; - textual FST display (`print net`)
;; - the command-line interface (tools.cli)

(ns cljfst.iface
  (:gen-class)
  (:require [clojure.pprint :refer [pprint]]
            [clojure.string :as string]
            [clojure.set :refer [union]]
            [clojure.tools.cli :refer [parse-opts]]
            [rhizome.viz :as viz]
            [cljfst.common :refer [epsilon-symbol
                                   identity-symbol
                                   pluralize-by-count
                                   unknown-symbol]]
            [cljfst.apply :refer [apply-down]]
            [cljfst.regex :refer [is-cyclic
                                  count-paths
                                  read-regex
                                  parse-to-fst]]
            [cljfst.determinize :refer [subset-construction]]))


;; AT&T Format --- Reading/Writing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn states-syms-att
  "Input: len-4 vector from AT&T line; output: vector of keywords (states) and
  strings (FST symbols)"
  [fields]
  (let [result
        (map-indexed
          (fn [idx itm]
            (if (< idx 2)
              (keyword (str "s" itm))
              (if (= itm "@_IDENTITY_SYMBOL_@")
                identity-symbol
                (if (= itm epsilon-symbol)
                  ""
                  itm))))
          fields)]
    result))

(defn process-line-att [line]
  "Process AT&T FST line: 4 tab-separated vals means input state, output state,
  input symbol, output symbol. One value means final state"
  (let [fields (string/split line #"\t")]
    (if (> (count fields) 3)
      (let [[st-i st-o sym-i sym-o] (states-syms-att fields)]
        {:delta #{[st-i sym-i st-o sym-o]}
         :sigma (set [sym-i sym-o])
         :Q (set [st-i st-o])})
      {:F #{(keyword (str "s" (first fields)))}})))

(defn add-att-line-to-fst
  "Return a new `fst` hash built by updating the passed-in one with the AT&T
  line"
  [fst line]
  (let [p-l (process-line-att line)]
    (assoc fst
           :delta (union (:delta fst) (get p-l :delta #{}))
           :sigma (union (:sigma fst) (get p-l :sigma #{}))
           :Q (union (:Q fst) (get p-l :Q #{}))
           :F (union (:F fst) (get p-l :F #{})))))

(defn parse-att
  "Parse AT&T-formatted FST file at `file-path` and return an FST hash map."
  [file-path]
  (with-open [rdr (clojure.java.io/reader file-path)]
    (reduce
      add-att-line-to-fst
      {:sigma #{}  ;; alphabet
       :Q #{}  ;; all states
       :s0 :s0  ;; designated start state
       :F #{}  ;; final states
       :delta #{}  ;; set of vectors: #{[st-i sym-i st-o sym-o] ...}
      }
      (line-seq rdr))))


;; GraphViz (dot) representations of FSA/FSTs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn get-graph-node-label
  "Return a hash for labeling `node`: double cirlce if it's final."
  [node fst]
  (if (some #{node} (:F fst))
    {:label (apply str (rest (str node)))
     :shape "doublecircle"}
    {:label (apply str (rest (str node)))
     :shape "circle"}))

(defn get-graph-edge-label
  "Return a hash for labeling the edge between nodes `n-src` and `n-dst`;
  something like '<a:b>'."
  [n-src n-dst fst]
  {:label
    (let [[_ inp __ outp]
          (first
            (filter
              (fn [[st-i sy-i st-o sy-o]]
                (and (= st-i n-src)
                     (= st-o n-dst)))
              (:delta fst)))]
      (str "<" inp ":" outp ">"))})

(defn view-fst
  "Use rhizome-viz (GraphViz) to display `fst` as a graph image."
  [fst]
  (let [nodes (:Q fst)
        adjacent (fn [node]
                   (reduce
                     (fn [adjs [st-i sy-i st-o sy-o]]
                       (if (= st-i node)
                         (conj adjs st-o)
                         adjs))
                     #{}
                     (:delta fst)))]
    (viz/view-graph nodes adjacent
                    :node->descriptor (fn [n] (get-graph-node-label n fst))
                    :edge->descriptor (fn [n-src n-dst]
                                        (get-graph-edge-label
                                          n-src n-dst fst)))))


;; FST Stack: FIFO data structure for holding user-defined FSTs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Holds the FSTs that the user has pushed to the stack.
(def cmd-stack (atom []))

(defn add-to-stack
  "Add the input `fst` to `cmd-stack`."
  [fst]
  (swap! cmd-stack
         (fn [current-cmd-stack]
           (conj current-cmd-stack fst))))

(defn get-top-fst
  "Return the last FST added to the stack."
  [] (last @cmd-stack))

(defn pop-stack
  "Remove top FST from cmd-stack."
  []
  (swap! cmd-stack
         (fn [current-cmd-stack]
           (if (> (count current-cmd-stack) 0)
            (pop current-cmd-stack)
            current-cmd-stack))))

(defn clear-stack
  "Remove all FSTs from cmd-stack."
  []
  (swap! cmd-stack (fn [current-cmd-stack] [])))


;; Textual FST representation (e.g., for `(print) net` command.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO:
;; - Get size of FST in bytes. For some ideas on how to get the size of a
;;   Clojure data structure in bytes, ;; see
;;   https://groups.google.com/forum/#!topic/clojure/dzelKZrIoH4
;; - If the FST is acyclic, count its paths and report them. A path is a
;;   sequence of arcs between a start state and an end state.

(defn get-cyclic-or-path-count
  [fst]
  (if (is-cyclic fst)
    ", Cyclic"
    (let [path-count (count-paths fst)]
      (str ", " path-count " " (pluralize-by-count "path" path-count)))))

(defn print-fst-stats
  "Print brief stats about the input fst. (foma reports look like '390 bytes. 1
  state, 4 arcs, Cyclic.')."
  [fst]
  (let [states (:Q fst)
        state-count (count states)
        arcs (:delta fst)
        arc-count (count arcs)
        cyclic-or-path-count (get-cyclic-or-path-count fst)]
    (println (str
               state-count
               " "
               (pluralize-by-count "state" state-count)
               ", "
               arc-count
               " "
               (pluralize-by-count "arc" arc-count)
               cyclic-or-path-count
               "."))))

(defn get-state-str-repr
  "Return a string representation of a state."
  [state fst]
  (let [is-final (some #{state} (:F fst))
        is-start (= state (:s0 fst))
        state-repr (string/replace (str state) ":" "")]
    (cond
      (and is-final is-start) (str "Sf" state-repr)
      is-start (str "S" state-repr)
      is-final (str "f" state-repr)
      :else state-repr)))

(defn clean-sym
  "Clean a symbol by converting internal representations of special symbols to
  user-facing ones."
  [sym]
  (get {unknown-symbol "?" identity-symbol "@" epsilon-symbol "0"} sym sym))

(defn get-outgoing-arcs
  "Return a string representation of the outgoing arcs from `state`."
  [state fst]
  (let [outgoing
        (filter (fn [[st-i & rest]] (= st-i state)) (:delta fst))
        outgoing
        (map
          (fn [[st-i sy-i st-o sy-o]]
            (let [sym-pair
                  (if (= sy-i sy-o)
                    (clean-sym sy-i)
                    (str (clean-sym sy-i) ":" (clean-sym sy-o)))]
              (str sym-pair " -> " (get-state-str-repr st-o fst))))
          outgoing)]
    (if (empty? outgoing)
      "(no arcs)"
      (string/join ", " outgoing))))

(defn get-arc-string
  "Return a string representation of the arcs in `fst`; something like
  'Ss0:a -> fs1.' or 'fs1:(no arcs)'."
  [fst]
  (string/join
    \newline
    (map
      (fn [state]
        (let [state-repr (get-state-str-repr state fst)
              outgoing-arcs (get-outgoing-arcs state fst)]
          (str state-repr ":\t" outgoing-arcs ".")))
      (sort (:Q fst)))))

(defn print-no-networks
  []
  (println "Not enough networks on stack. Operation requires at least 1."))

(defn get-sigma-str
  "Return a string representation of the alphabet of `fst`."
  [fst]
  (let [cleaned-sigma (map clean-sym (:sigma fst))]
    (str "Sigma: " (string/join " " cleaned-sigma))))

(defn print-net
  "Print detailed information about the top fst on the stack.
  Foma does::
    Sigma: a
    Size: 1.
    Net: 1265003F
    Flags: deterministic pruned minimized epsilon_free loop_free arcs_sorted_in arcs_sorted_out 
    Arity: 1
    Ss0:a -> fs1.
    fs1:(no arcs)."
  ([] (print-net (get-top-fst)))
  ([fst]
    (if fst
      (let [sigma (get-sigma-str fst)
            arc-string (get-arc-string fst)]
        (println (string/join \newline [sigma arc-string])))
      (print-no-networks))))


;; Command-line Interface functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This controls what happens at the "cljfst[0]:" prompt. Uses the tools.cli
;; library.

;; TODO:
;; - readline-like functionality (JLine?) for using up/down arrows to get
;;   command history.

(def cli-options
  [["-v" "--version"]
   ["-h" "--help"]])

(defn usage
  "Return a multi-line string describing how to use Clojure FST."
  [options-summary]
  (->> ["Clojure FST -- finite-state transducer toolkit"
        ""
        "Usage: program-name [options]"
        ""
        "Options:"
        options-summary]
       (string/join \newline)))

(defn error-msg
  "Return a string representation of `errors`."
  [errors]
  (str "The following errors occurred while parsing your command:\n\n"
       (string/join \newline errors)))

(defn exit
  "Print `msg` and exit/quit the program."
  [status msg]
  (println msg)
  (System/exit status))

(defn regex->stack
  "Parse the string `val` as a regex and add it to the global `cmd-stack`
  stack."
  [val]
  (let [parse (read-regex val)
        fst (parse-to-fst parse)
        determinized-fst (subset-construction fst)]
    (print-fst-stats fst)
    (add-to-stack fst)))

(defn unknown-input
  "User has entered an unknown command."
  ([] (println "Yeah, um, sorry. What?"))
  ([input] (println (str "Yeah, um, sorry. What does " input " mean?"))))

(defn apply-down-top-fst
  "Return the result of performing apply-down on the top FST on the stack."
  [input-string]
  (let [fst (get-top-fst)]
    (if fst
      (println (string/join \newline (apply-down fst input-string)))
      (print-no-networks))))

(defn remove-cmd-prefix
  "Remove the commnad prefix from a user-specified command, e.g., convert
  'regex a -> b || c _ d ;' to 'a -> b || c _ d ;'."
  [input prefix]
  (string/trim (string/replace-first input prefix "")))

(defn parse-user-input
  "Parse user input at the command line and respond to it."
  [input]
  (cond
    (string/starts-with? input "clear") (clear-stack)
    (string/starts-with? input "down") (apply-down-top-fst (remove-cmd-prefix input "down"))
    (string/starts-with? input "net") (print-net)
    (string/starts-with? input "pop") (pop-stack)
    (string/starts-with? input "quit") (exit 0 "Goodbye.")
    (string/starts-with? input "regex") (regex->stack (remove-cmd-prefix input "regex"))
    :else (unknown-input input)))

(defn print-prompt
  "Print the 'cljfst[0]: ' prompt."
  []
  (print (str "cljfst[" (count @cmd-stack) "]: ")))

(defn get-input
  "Display cljfst[0]: prompt and wait for the user to enter commands and hit
  enter."
  []
  (let [input
        (do
          (print-prompt)
          (flush)
          (try
            (string/trim (read-line))
            (catch Exception e (exit 0 "Goodbye."))))]
    (if (empty? input)
      (get-input)
      (do
        (parse-user-input input)
        (get-input)))))

(defn cljfst-cli
  [& args]
  (let [{:keys [options arguments errors summary]}
        (parse-opts args cli-options)]
    (cond
      (:help options) (exit 0 (usage summary))
      (:version options) (exit 0 "Clojure FST has version yet.")
      (not= (count arguments) 0) (exit 1 (usage summary))
      errors (exit 1 (error-msg errors)))
    (get-input)))
