# Proof cleanup

* Merge `εStep` and `charStep`
* Embed inBounds to NFA definition
  * Simplifies the correcness proof of the graph traversals

# Performance optimization

* Add this to BurntSushi/rebar for benchmarking
* Check generated code
  * inline `NFA.get` and `NodeSet.get/set`
* Reuse allocations
  * Q: if we return a pair, does it cause Lean to allocate/destroy it repeatedly?
* Lazy DFA
  * It requires byte-level state machines though...

# Functionalities

* Regex parser
* Character classes
* Capture groups

# Misc

* Remove Mathlib dependency (at least from the computational part)
