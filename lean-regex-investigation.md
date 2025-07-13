# Lean-Regex Library Investigation

## Overview

The **lean-regex** library is a Lean 4 implementation of regular expressions with formal verification of correctness. The main repository is [`bergmannjg/regex`](https://github.com/bergmannjg/regex), which implements a PCRE2-compatible regular expression engine written in Lean 4.

### Key Features
- **PCRE2 Compatibility**: Extended for compatibility with PCRE2 syntax
- **Unicode Support**: Focus on Unicode data handling  
- **Formal Verification**: Provides formal verification of correctness
- **BoundedBacktracker**: Uses a single regex engine implementation
- **Compile-time Regex**: Supports `regex%` notation for compile-time regex building
- **Comprehensive Testing**: Tested against PCRE2 and Rust regex test suites

### Repository Structure
- **Regex/**: Core regex implementation modules
- **test/**: Test suites and test data
- **testdata/**: Test data from PCRE2 and Rust regex
- **benchmark/**: Performance benchmarking code
- **scripts/**: Build and utility scripts
- **docbuild/**: Documentation generation

## Related Work

Several other Lean 4 regex-related projects exist:
- [`ezhuchko/extended-regexes`](https://github.com/ezhuchko/extended-regexes): Extended regex with lookarounds
- [`katydid/regex-deriv-lean`](https://github.com/katydid/regex-deriv-lean): Regex derivatives proofs
- [`Agnishom/lregex`](https://github.com/Agnishom/lregex): Verified regex matching with lookaround

## 10 Good First Issues

### 1. **Documentation: Add Examples to README**
**Difficulty**: Beginner  
**Skills**: Documentation, Lean 4 syntax

Add more comprehensive examples to the README showing:
- Basic regex usage patterns
- Unicode character matching examples
- Performance comparisons with other regex engines
- Integration examples with Lean 4 projects

**Why good for beginners**: Requires understanding the library API without needing to modify core code.

### 2. **Testing: Add Property-Based Tests**
**Difficulty**: Beginner to Intermediate  
**Skills**: Testing, Property-based testing

Implement property-based tests using Lean 4's testing framework:
- Generate random strings and verify regex matching properties
- Test regex equivalence properties
- Add tests for edge cases in Unicode handling

**Why good for beginners**: Tests are isolated and help understand the library's behavior.

### 3. **Performance: Benchmark Against Standard Libraries**
**Difficulty**: Beginner to Intermediate  
**Skills**: Benchmarking, Performance analysis

Expand the existing benchmark suite:
- Add comparisons with other regex engines (when possible)
- Create micro-benchmarks for specific regex patterns
- Add memory usage profiling
- Document performance characteristics

**Why good for beginners**: Focuses on measurement rather than implementation.

### 4. **Feature: Add Basic Regex Builder API**
**Difficulty**: Intermediate  
**Skills**: API design, Lean 4 programming

Create a fluent API for building regexes programmatically:
```lean
let regex := RegexBuilder.new
  |>.literal("hello")
  |>.oneOrMore(RegexBuilder.digit)
  |>.optional(RegexBuilder.whitespace)
  |>.build()
```

**Why good for beginners**: Well-defined scope with clear requirements.

### 5. **Tooling: Add Regex Validation and Debugging**
**Difficulty**: Intermediate  
**Skills**: Error handling, User experience

Implement better error reporting and debugging tools:
- Detailed error messages for invalid regex patterns
- Regex pattern visualization/explanation
- Debug mode showing matching steps
- Syntax highlighting for regex patterns

**Why good for beginners**: Focuses on user experience improvements.

### 6. **Feature: Implement Common Regex Shortcuts**
**Difficulty**: Beginner to Intermediate  
**Skills**: Pattern matching, Lean 4 syntax

Add convenience functions for common regex operations:
- `isEmail(s: String): Bool`
- `isURL(s: String): Bool`
- `isIPAddress(s: String): Bool`
- `extractNumbers(s: String): List String`

**Why good for beginners**: Small, focused features with clear specifications.

### 7. **Testing: Improve Test Coverage**
**Difficulty**: Beginner  
**Skills**: Testing, Lean 4

Identify and add tests for uncovered code paths:
- Add tests for error conditions
- Test edge cases in Unicode handling
- Add regression tests for reported bugs
- Test performance edge cases

**Why good for beginners**: Helps understand codebase while improving quality.

### 8. **Documentation: Add Formal Verification Examples**
**Difficulty**: Intermediate  
**Skills**: Formal methods, Lean 4 proofs

Create examples showing the formal verification aspects:
- Prove properties about simple regex patterns
- Document the correctness guarantees
- Show how to use the verification in practice
- Create tutorial on regex verification

**Why good for beginners**: Good introduction to formal verification in Lean 4.

### 9. **Feature: Add Regex Compilation Cache**
**Difficulty**: Intermediate  
**Skills**: Caching, Performance optimization

Implement caching for compiled regex patterns:
- Cache compiled patterns to avoid recompilation
- Add cache invalidation strategies
- Measure performance improvements
- Add cache size limits and eviction policies

**Why good for beginners**: Well-defined feature with measurable benefits.

### 10. **Integration: Add Lake Template/Example Project**
**Difficulty**: Beginner  
**Skills**: Project structure, Lake build system

Create a template project showing how to use lean-regex:
- Lake project template with regex dependency
- Example applications using the library
- Integration with other Lean 4 libraries
- Documentation for project setup

**Why good for beginners**: Focuses on project structure and integration.

## Getting Started

### Prerequisites
- Lean 4 installation (latest stable version)
- Lake build system
- Basic understanding of regular expressions
- Familiarity with Lean 4 syntax

### Development Setup
1. Clone the repository: `git clone https://github.com/bergmannjg/regex`
2. Run tests: `lake test`
3. Build documentation: `lake build`
4. Run benchmarks: `lake run benchmark`

### Contributing Guidelines
- Follow existing code style and patterns
- Add tests for new features
- Update documentation
- Ensure all tests pass
- Keep changes focused and atomic

## Conclusion

The lean-regex library provides an excellent opportunity to contribute to a practical Lean 4 project with formal verification aspects. The suggested issues range from beginner-friendly documentation and testing improvements to more advanced features requiring deeper Lean 4 knowledge. Contributors can choose issues that match their experience level and interests while helping improve a valuable tool for the Lean 4 ecosystem.