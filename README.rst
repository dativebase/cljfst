===============================================================================
  cljfst --- Clojure Finite-state Transducer Tookit
===============================================================================

Finite-state toolkit written in Clojure. Based on foma
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
apply-down on input strings. To open the cljfst REPL::

    $ lein run
    cljfst[0]:

define a regex and run apply-down on a string; for example::

    cljfst[0]: regex [a:x|b:y c]* ;
    4 states, 7 arcs, Cyclic.
    cljfst[1]: down abcabcabcabcbcbc
    xycxycxycxycycyc

To generate the uberjar (a single jar file that contains the contents of all
of the dependencies)::

    $ lein uberjar

To run the .jar file::

    $ java -jar target/uberjar/cljfst-0.1.0-SNAPSHOT-standalone.jar
    cljfst[0]:


Tests
===============================================================================

To run the tests from the command-line::

    $ lein test


Installation
===============================================================================

To do.
