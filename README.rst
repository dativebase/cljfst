===============================================================================
  cljfst --- Clojure Finite-state Transducer Tookit
===============================================================================

Finit-state toolkit written in Clojure. Based on foma
https://github.com/mhulden/foma.

At this point, cljfst is just a toy for learning Clojure and FSTs for NLP.


Current State
===============================================================================

Incomplete. Current task(s) and references:

- current task: implementing Hopcroft canonical minimization algorithm (Hulden,
  p. 80)
- instaparse reference: https://github.com/Engelberg/instaparse
- foma reference:
  https://github.com/mhulden/foma/blob/master/foma/docs/simpleintro.md


Usage
===============================================================================

At present, cljfst can compile simple transducer regexes and use them to run
apply-down on input strings. To defin a regex and run apply-down on a string::

    $ lein run <regex> <string>

For example::

    $ lein run "regex [a:x|b:y c]* ;" abcabcabcabcbcbc
    xycxycxycxycycyc

To play with cljfst in the REPL::

    $ cd cljfst
    $ lein repl
    cljfst.core=> (require 'cljfst.core)
    cljfst.core=> (cljfst.core/-main "regex a:b ;" "a")
    b

To generate the uberjar (a single jar file that contains the contents of all
of the dependencies)::

    $ lein uberjar

To run the .jar file::

    $ java -jar target/uberjar/cljfst-0.1.0-SNAPSHOT-standalone.jar "regex l:r e i:p n:l ;" lein
    repl


Tests
===============================================================================

To run the tests from the command-line::

    $ lein test

To run the tests from within the REPL::

    $ cd cljfst
    $ lein repl
    cljfst.core=> (require '[clojure.test :refer [run-tests]])
    cljfst.core=> (require 'cljfst.core-test)
    cljfst.core=> (run-tests 'cljfst.core-test)

After chaning the tests, you can refresh and rerun them via::

    cljfst.core=> (require 'cljfst.core-test :reload-all)
    cljfst.core=> (run-tests 'cljfst.core-test)


Installation
===============================================================================

To do.

