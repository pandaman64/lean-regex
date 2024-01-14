# Proof cleanup

* Merge `εStep` and `charStep`
* `inBounds` should prove something like `j \in nfa.step i c \r j < nfa.nodes.size`
  * NewNodesRange should follow a similar pattern
* Embed inBounds to NFA definition
  * Simplifies the correcness proof of the graph traversals

# Performance optimization

* Add this to BurntSushi/rebar for benchmarking
  * Depends on search
* Check generated code
  * inline `NFA.get` and `NodeSet.get/set`
* Reuse allocations
  * Q: if we return a pair, does it cause Lean to allocate/destroy it repeatedly?
* Lazy DFA
  * It requires byte-level state machines though...

# Functionalities

* Implement search
* Regex parser
* Character classes
* Capture groups
