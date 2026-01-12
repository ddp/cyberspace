(rfc
  (number 55)
  (title "Compilation and Debugging Manual")
  (section
    "Abstract"
    (p "This RFC is the compilation and debugging manual for Cyberspace Scheme. It specifies type inference conventions, build system architecture, debugging infrastructure, exception handling, and inspector design. The guiding principles are Ada's \"declare everything, infer nothing\" and Dylan's \"inspect everything, hide nothing.\""))

  (section
    "Part I: Compilation"
    (p ""))

  (section
    "1. Type System Overview"
    (subsection
      "1.1 Chicken's Scrutinizer"
      (p "Chicken Scheme includes a flow-sensitive type analyzer called the scrutinizer. When invoked with -strict-types, it performs whole-program type inference and reports errors when types cannot be proven safe.")
      (p "The scrutinizer tracks type information through:")
      (list
        "Variable bindings and assignments"
        "Conditional branches (if, cond, case)"
        "Procedure calls and returns"
        "Special forms (let, let*, letrec)"))
    (subsection
      "1.2 The Inference Problem"
      (p "Whole-program type inference without declarations can exhibit exponential complexity. The scrutinizer's flow-sensitive analysis becomes intractable when:")
      (list
        "Functions contain many conditional branches with side effects"
        "Format strings (sprintf) create implicit polymorphic constraints"
        "Type information cannot flow through set! mutations"
        "Multiple paths merge with incompatible inferred types")
      (p "Empirical observation: A function with 30 conditional sprintf calls can take 5+ minutes to analyze. The same function with type declarations compiles in under 1 second."))
    (subsection
      "1.3 The Ada Principle"
      (p "Ada's compilation model requires explicit type declarations everywhere. The compiler is a checker, not a guesser. Jean Ichbiah's design traded verbosity for predictability - when Ada compiles, it tends to run correctly.")
      (p "For Cyberspace modules, we adopt this principle:")
      (code "DECLARE EVERYTHING, INFER NOTHING")
      (p "Benefits:")
      (list
        "Predictable compilation times"
        "Better error messages (mismatch against declaration, not inference)"
        "Documentation of programmer intent"
        "Enables separate compilation")))

  (section
    "2. Type Declaration Conventions"
    (subsection
      "2.1 Required Import"
      (p "Modules using type declarations must import the type system:")
      (code scheme "(import (chicken type))")
      (p "Place this import with other chicken imports, before srfi and cyberspace modules."))
    (subsection
      "2.2 Declaration Placement"
      (p "Type declarations are placed in a dedicated section after imports, before any function definitions:")
      (code scheme "(module example
  (export1 export2)

  (import scheme
          (chicken base)
          (chicken type)
          ...)

  ;;; ============================================================
  ;;; Type Declarations
  ;;; ============================================================

  (: export1 (string -> boolean))
  (: export2 (fixnum fixnum -> fixnum))
  (: internal-helper (list -> (or string false)))

  ;;; ============================================================
  ;;; Implementation
  ;;; ============================================================

  (define (export1 s) ...)
  ...)"))
    (subsection
      "2.3 Declaration Syntax"
      (p "The (: name type) form declares the type of a binding:")
      (code scheme ";; Simple function types
(: add1 (fixnum -> fixnum))
(: string-empty? (string -> boolean))

;; Multiple arguments
(: substring (string fixnum fixnum -> string))

;; Optional arguments
(: open-file (string #!optional symbol -> port))

;; Rest arguments
(: format (string #!rest * -> string))

;; Union types
(: find-item (symbol -> (or item false)))

;; Procedures as arguments
(: map-items ((item -> result) (list-of item) -> (list-of result)))

;; No return (exits or loops forever)
(: fatal-error (string -> noreturn))"))
    (subsection
      "2.4 Common Type Names"
      (table
        (header "Type" "Description" "Example Values")
        (row "fixnum" "Small exact integer" "0, 42, -17")
        (row "flonum" "Floating point" "3.14, -2.5e10")
        (row "number" "Any number" "fixnum or flonum")
        (row "string" "Character string" "\"hello\"")
        (row "symbol" "Symbolic atom" "'foo, 'bar")
        (row "boolean" "Truth value" "#t, #f")
        (row "char" "Single character" "#\\a, #\\newline")
        (row "list" "Proper list" "'(1 2 3)")
        (row "(list-of T)" "Homogeneous list" "(list-of string)")
        (row "pair" "Cons cell" "'(a . b)")
        (row "vector" "Fixed-size array" "#(1 2 3)")
        (row "blob" "Byte vector" "(make-blob 16)")
        (row "port" "I/O port" "(current-input-port)")
        (row "procedure" "Any procedure" "car, +")
        (row "(T1 -> T2)" "Specific procedure" "(string -> fixnum)")
        (row "(or T1 T2)" "Union type" "(or string false)")
        (row "(struct name)" "C struct wrapper" "(struct tcp-listener)")
        (row "false" "The #f value" "#f")
        (row "*" "Any type" "anything")
        (row "noreturn" "Never returns" "for exit, error")))
    (subsection
      "2.5 When Declarations Are Required"
      (p "Type declarations are REQUIRED for:")
      (list
        "Functions with more than 5 conditional branches"
        "Functions using set! on local variables"
        "Functions with multiple sprintf/format calls"
        "All exported (public API) functions"
        "Functions that call other modules' exported functions")
      (p "Type declarations are OPTIONAL for:")
      (list
        "Simple leaf functions (< 5 lines, no branching)"
        "Local helper functions with obvious types"
        "Functions used only in one place")))

  (section
    "3. Typed Helper Pattern"
    (subsection
      "3.1 The Problem"
      (p "A common pattern causes exponential inference:")
      (code scheme ";; BAD: Exponential type inference
(define (session-summary)
  (let ((stats '()))
    (when (> (session-stat 'reads) 0)
      (set! stats (cons (sprintf \"~a read~a\"
                                  (session-stat 'reads)
                                  (if (= 1 (session-stat 'reads)) \"\" \"s\"))
                        stats)))
    (when (> (session-stat 'writes) 0)
      (set! stats (cons (sprintf \"~a write~a\" ...) stats)))
    ;; ... 28 more similar blocks ...
    (reverse stats)))")
      (p "The scrutinizer must analyze all 2^30 possible paths through this function."))
    (subsection
      "3.2 The Solution"
      (p "Factor into small typed helpers:")
      (code scheme ";; GOOD: Linear type inference
(: format-stat (symbol string string -> (or string false)))
(define (format-stat key singular plural-suffix)
  \"Format a session stat with pluralization, or #f if zero.\"
  (let ((n (session-stat key)))
    (if (> n 0)
        (string-append (number->string n) \" \" singular
                       (if (= n 1) \"\" plural-suffix))
        #f)))

(: format-stat-irregular (symbol string string -> (or string false)))
(define (format-stat-irregular key singular plural)
  \"Format with irregular plural.\"
  (let ((n (session-stat key)))
    (if (> n 0)
        (string-append (number->string n) \" \"
                       (if (= n 1) singular plural))
        #f)))

(: session-summary (-> (list-of string)))
(define (session-summary)
  \"Generate session statistics summary.\"
  (filter identity
    (list
      (format-stat 'reads \"read\" \"s\")
      (format-stat 'writes \"write\" \"s\")
      (format-stat-irregular 'queries \"query\" \"queries\")
      ...)))")
      (p "Each helper is independently typed. The scrutinizer analyzes them separately, giving O(n) instead of O(2^n) complexity."))
    (subsection
      "3.3 Composition via filter"
      (p "The pattern (filter identity (list ...)) collects non-#f results:")
      (code scheme "(filter identity (list \"a\" #f \"b\" #f \"c\"))
;; => (\"a\" \"b\" \"c\")")
      (p "This replaces imperative set!/cons accumulation with functional composition.")))

  (section
    "4. Build System Architecture"
    (subsection
      "4.1 The Forge"
      (p "The forge is the build system for Cyberspace modules. It compiles Scheme to shared libraries (.so) with import specifications (.import.scm).")
      (p "Invocation:")
      (code scheme "(bootstrap-modules!)  ; Called automatically at REPL start")
      (p "Output format:")
      (code "+---------------- forge: portal ----------------+
| csc -shared -J -strict-types portal.scm      |
| > 241K + 677B import in 921ms                |
+-----------------------------------------------+"))
    (subsection
      "4.2 Compiler Invocation"
      (p "The forge invokes csc (Chicken Scheme Compiler) with these flags:")
      (table
        (header "Flag" "Purpose")
        (row "-shared" "Produce shared library (.so)")
        (row "-J" "Generate import library (.import.scm)")
        (row "-strict-types" "Enable scrutinizer type checking (beta)")
        (row "-I path" "Add include path (for FFI)")
        (row "-L path" "Add library path (for FFI)")
        (row "-l lib" "Link library (e.g., -lsodium)"))
      (p "Example invocations:")
      (code shell "# Standard module
csc -shared -J -strict-types portal.scm

# FFI module with libsodium
csc -shared -J -strict-types crypto-ffi.scm \\
    -I/opt/homebrew/include -L/opt/homebrew/lib -lsodium"))
    (subsection
      "4.3 Dependency Levels"
      (p "Modules are organized into dependency levels. Modules within a level have no mutual dependencies and compile in parallel.")
      (code scheme ";; Level 0: Foundation (no cyberspace dependencies)
(\"os\" \"crypto-ffi\" \"sexp\" \"capability\")

;; Level 1: Core utilities (depend on Level 0 only)
(\"mdns\" \"fips\" \"audit\" \"wordlist\" \"bloom\"
 \"catalog\" \"keyring\" \"portal\")

;; Level 2: Certificates and enrollment (depend on Levels 0-1)
(\"cert\" \"enroll\")

;; Level 3: Protocols (depend on Levels 0-2)
(\"gossip\" \"security\")

;; Level 4: High-level operations (depend on Levels 0-3)
(\"vault\" \"auto-enroll\")

;; Level 5: User interface (depend on all prior)
(\"ui\")")
      (p "To determine a module's level, examine its imports:")
      (list
        "If it imports only chicken/srfi modules: Level 0"
        "If it imports Level 0 modules: Level 1"
        "If it imports Level N modules: Level N+1 or higher"))
    (subsection
      "4.4 Parallel Compilation"
      (p "Each level compiles in parallel using process-fork:")
      (code scheme "(define (rebuild-level-parallel! modules)
  (let ((pids (map (lambda (module)
                     (process-fork
                       (lambda ()
                         (rebuild-module! module)
                         (exit 0))))
                   modules)))
    (for-each process-wait pids)
    (length modules)))")
      (p "The build blocks until all processes in a level complete before starting the next level. This ensures dependencies are satisfied."))
    (subsection
      "4.5 Rebuild Detection"
      (p "A module needs rebuilding when any of these conditions hold:")
      (list
        "The .so file does not exist"
        "The .import.scm file does not exist"
        "The source .scm is newer than the .so (mtime comparison)"
        "The platform stamp doesn't match (e.g., Darwin-arm64 vs Linux-x86_64)")
      (code scheme "(define (needs-rebuild? module)
  (or (not (file-exists? (string-append module \".so\")))
      (not (file-exists? (string-append module \".import.scm\")))
      (> (file-mtime (string-append module \".scm\"))
         (file-mtime (string-append module \".so\")))
      (not (string=? (read-arch-stamp module) (current-arch)))))")))

  (section
    "5. Beta vs Production Builds"
    (subsection
      "5.1 Build Mode Flag"
      (p "The *beta-build* flag controls strict type checking:")
      (code scheme ";; In cyberspace-repl.scm
(define *beta-build* #t)  ; Enable for development
(define *beta-build* #f)  ; Disable for release"))
    (subsection
      "5.2 Beta Mode Benefits"
      (p "With *beta-build* = #t:")
      (list
        "All modules compile with -strict-types"
        "Type mismatches are compile-time errors"
        "Invalid arguments are detected"
        "Deprecated identifiers are flagged"
        "Format string errors are caught")
      (p "Build time impact: ~20-25 seconds for full rebuild"))
    (subsection
      "5.3 Production Mode"
      (p "With *beta-build* = #f:")
      (list
        "Modules compile without -strict-types"
        "Type declarations remain as documentation"
        "Faster compilation"
        "Smaller binaries (no type metadata)")
      (p "Build time impact: ~10-15 seconds for full rebuild"))
    (subsection
      "5.4 When to Use Each Mode"
      (table
        (header "Scenario" "Mode" "Rationale")
        (row "Active development" "Beta" "Catch type errors early")
        (row "CI/CD pipeline" "Beta" "Prevent type regressions")
        (row "Release builds" "Production" "Optimize for users")
        (row "Debugging issues" "Beta" "Better error context")
        (row "Performance testing" "Production" "Measure real performance"))))

  (section
    "Part II: Debugging"
    (p ""))

  (section
    "6. Exception Handling"
    (subsection
      "6.1 Condition System"
      (p "Chicken uses the SRFI-12 condition system. Exceptions are condition objects with properties:")
      (code scheme "(handle-exceptions exn
  ;; Handler: exn is the condition object
  (print \"Error: \" (get-condition-property exn 'exn 'message))

  ;; Protected code
  (dangerous-operation))")
    (subsection
      "6.2 Standard Condition Properties"
      (table
        (header "Property" "Type" "Description")
        (row "'exn 'message" "string" "Human-readable error message")
        (row "'exn 'location" "symbol" "Procedure where error occurred")
        (row "'exn 'arguments" "list" "Arguments that caused error")
        (row "'exn 'call-chain" "list" "Stack trace"))
      (code scheme "(define (safe-operation x)
  (handle-exceptions exn
    (let ((msg (get-condition-property exn 'exn 'message \"unknown\"))
          (loc (get-condition-property exn 'exn 'location #f))
          (chain (get-condition-property exn 'exn 'call-chain '())))
      (printf \"Error in ~a: ~a~n\" loc msg)
      (print-call-chain chain)
      #f)
    (actual-operation x)))"))
    (subsection
      "6.3 Rich Exception Display"
      (p "The REPL provides rich exception display with box formatting:")
      (code "+-------------- Exception ---------------+
| division by zero                       |
| Location: quotient                     |
| Arguments: (42 0)                      |
+-----------------------------------------+
| Call Chain:                            |
|   divide-values                        |
|   process-input                        |
|   main-loop                            |
+-----------------------------------------+")
      (p "Implementation uses the centralized box-drawing API from os.scm.")))

  (section
    "7. Tracing and Profiling"
    (subsection
      "7.1 Procedure Tracing"
      (p "Trace procedure calls and returns:")
      (code scheme ";; Enable tracing
(trace foo)
(trace bar baz)

;; Disable tracing
(untrace foo)
(untrace)  ; untrace all")
      (p "Trace output:")
      (code "(foo 1 2 3)
  |(bar 1)
  | (baz 2)
  | baz -> 4
  |bar -> 5
foo -> 8"))
    (subsection
      "7.2 REPL Trace Commands"
      (p "CSI provides trace commands:")
      (code ",trace proc     ; trace procedure
,trace         ; show traced procedures
,untrace proc  ; stop tracing
,untrace       ; stop all tracing"))
    (subsection
      "7.3 Call Chain"
      (p "Get the current call chain at any point:")
      (code scheme "(define (debug-here)
  (print-call-chain (get-call-chain)))

;; Or after an error in the REPL:
,n              ; show call chain
,c              ; continue
,d              ; describe exception"))
    (subsection
      "7.4 Time Profiling"
      (p "Measure execution time:")
      (code scheme "(time (expensive-operation))
;; => 0.142s CPU, 0.145s real, 12345 bytes allocated")
      (p "For more detailed profiling, compile with -profile and use chicken-profile.")))

  (section
    "8. Inspector Design"
    (p "Inspired by Dylan's inspector - the gold standard for interactive debugging.")
    (subsection
      "8.1 Design Principles"
      (p "The Dylan inspector philosophy:")
      (list
        "INSPECT EVERYTHING: Any object can be inspected"
        "HIDE NOTHING: Internal structure is visible"
        "NAVIGATE FREELY: Drill down into any component"
        "MODIFY CAREFULLY: Live patching with safety checks"
        "HISTORY MATTERS: Navigation history, bookmarks"))
    (subsection
      "8.2 Inspector Commands (Planned)"
      (table
        (header "Command" "Action")
        (row ":i obj" "Inspect object")
        (row ":s" "Show current object")
        (row ":d N" "Descend into slot N")
        (row ":u" "Up to parent object")
        (row ":h" "Show inspection history")
        (row ":b" "Bookmark current object")
        (row ":m slot val" "Modify slot value")
        (row ":t" "Show object type info")
        (row ":r" "Show references to object")))
    (subsection
      "8.3 Object Display Format"
      (code "+---------- Inspecting: pair -------------+
| Type: pair                             |
| Address: 0x7fff5fbff8a0                |
+-----------------------------------------+
| [0] car: symbol 'foo                   |
| [1] cdr: pair (...)                    |
+-----------------------------------------+
| :d 0  - inspect car                    |
| :d 1  - inspect cdr                    |
| :u    - go back                        |
+-----------------------------------------+"))
    (subsection
      "8.4 Type-Specific Inspectors"
      (p "Specialized display for common types:")
      (list
        "Procedures: arity, source location, closure variables"
        "Ports: direction, filename, position"
        "Blobs: hex dump, ASCII preview"
        "Hash tables: key count, load factor, entries"
        "SPKI certs: issuer, subject, validity, delegation"
        "Audit entries: timestamp, actor, operation")))

  (section
    "9. REPL Debugging Commands"
    (subsection
      "9.1 Built-in Commands"
      (table
        (header "Command" "Description")
        (row ",?" "Show help")
        (row ",l file" "Load file")
        (row ",r" "Show recent expressions")
        (row ",s" "Show current module")
        (row ",m module" "Enter module")
        (row ",n" "Show call chain after error")
        (row ",d" "Describe last exception")
        (row ",c" "Continue after break")
        (row ",q" "Quit REPL")
        (row ",t proc" "Trace procedure")
        (row ",u proc" "Untrace procedure")))
    (subsection
      "9.2 Cyberspace Extensions"
      (table
        (header "Command" "Description")
        (row ":rebuild" "Force rebuild all modules")
        (row ":status" "Show session statistics")
        (row ":soup" "Enter soup browser")
        (row ":inspect obj" "Inspect object (planned)")
        (row ":audit" "Show recent audit entries")
        (row ":keys" "Show loaded keys")))
    (subsection
      "9.3 Error Recovery"
      (p "After an error, the REPL captures context:")
      (code "> (/ 1 0)
+-------------- Exception ---------------+
| division by zero                       |
+-----------------------------------------+

> ,n
Call chain:
  (/ 1 0)
  <toplevel>

> ,d
Condition: exn
  message: \"division by zero\"
  location: /
  arguments: (1 0)")))

  (section
    "10. Compiler Warnings Reference"
    (subsection
      "10.1 Type Warnings"
      (code "Warning: Invalid argument
  Argument #1 to procedure `tcp-accept' has an invalid type:
    false
  The expected type is:
    (struct tcp-listener)")
      (p "Fix: Add type check or adjust control flow to ensure correct type."))
    (subsection
      "10.2 Deprecation Warnings"
      (code "Warning: Deprecated identifier `current-milliseconds'
  Use of deprecated identifier from module `chicken.time'.")
      (p "Fix: Use current-process-milliseconds instead."))
    (subsection
      "10.3 Format String Warnings"
      (code "Warning: `printf', in format string \"~.2f\",
  illegal format-string character `.'")
      (p "Fix: Chicken format doesn't support precision specifiers. Use manual rounding."))
    (subsection
      "10.4 Redefinition Warnings"
      (code "Warning: redefinition of imported value binding: blob=?")
      (p "Fix: Either don't redefine, or explicitly shadow with (only (chicken blob) (not blob=?))"))
    (subsection
      "10.5 Warning Policy"
      (p "For production code:")
      (list
        "Zero warnings is the goal"
        "All warnings should be investigated"
        "Known acceptable warnings should be documented"
        "CI should fail on new warnings")))

  (section
    "11. Performance Tuning"
    (subsection
      "11.1 Compilation Performance"
      (table
        (header "Module Size" "Without -strict-types" "With -strict-types")
        (row "< 500 LOC" "~500ms" "~700ms")
        (row "500-2000 LOC" "~1s" "~2s")
        (row "> 2000 LOC (typed)" "~2s" "~7s")
        (row "> 2000 LOC (untyped)" "~2s" "exponential"))
      (p "Full bootstrap (21 modules): ~20-25s with strict types"))
    (subsection
      "11.2 Runtime Performance"
      (p "Type declarations have no runtime cost - they're only used at compile time.")
      (p "For runtime optimization:")
      (list
        "Use fixnum operations for integer math (fx+, fx<, etc.)"
        "Use flonum operations for float math (fp+, fp<, etc.)"
        "Avoid unnecessary string allocation"
        "Prefer vectors over lists for random access"
        "Use hash tables for lookup-heavy operations"))
    (subsection
      "11.3 Memory Profiling"
      (p "Track allocations:")
      (code scheme "(gc #t)  ; Force GC and print statistics
(memory-statistics)  ; Show current memory use")
      (p "For detailed profiling, compile with -profile flag.")))

  (section
    "12. Module Conventions"
    (subsection
      "12.1 File Structure"
      (code scheme ";;; module.scm - One line description
;;;
;;; Longer description of purpose, heritage, references.
;;;
;;; Copyright (c) 2026 Author. See LICENSE.

(module module-name
  (;; Exports grouped by category
   export1
   export2

   ;; Internal (for testing/debugging)
   internal-helper)

  (import scheme
          (chicken base)
          (chicken type)
          ...)

  ;;; ============================================================
  ;;; Type Declarations
  ;;; ============================================================

  (: export1 ...)
  (: export2 ...)

  ;;; ============================================================
  ;;; Section Name
  ;;; ============================================================

  (define (export1 ...) ...)

) ; end module"))
    (subsection
      "12.2 Naming Conventions"
      (table
        (header "Type" "Convention" "Example")
        (row "Procedure" "verb-noun" "read-file, parse-cert")
        (row "Predicate" "noun?" "empty?, valid-cert?")
        (row "Conversion" "x->y" "string->blob, cert->sexp")
        (row "Mutator" "verb!" "set-value!, init!")
        (row "Constant" "*name*" "*default-port*, *max-retries*")
        (row "Parameter" "current-name" "current-realm, current-principal")))
    (subsection
      "12.3 Documentation Strings"
      (p "All exported procedures should have docstrings:")
      (code scheme "(define (read-file path)
  \"Read entire file contents as string.
   Returns #f if file doesn't exist.\"
  ...)")))

  (section
    "13. Testing Conventions"
    (subsection
      "13.1 Test File Location"
      (p "Tests live alongside source:")
      (code "module.scm       ; Source
module-test.scm  ; Tests"))
    (subsection
      "13.2 Test Structure"
      (code scheme "(import module)
(import test)  ; SRFI-64 or similar

(test-begin \"module\")

(test-group \"feature-name\"
  (test-equal \"description\" expected (actual))
  (test-assert \"predicate\" (condition?)))

(test-end \"module\")"))
    (subsection
      "13.3 Running Tests"
      (code shell "csi -s module-test.scm")))

  (section
    "14. References"
    (list
      "Chicken Scheme User's Manual: Types"
      "Chicken Scheme User's Manual: Debugging"
      "SRFI-12: Exception Handling"
      "Ada Reference Manual: Type System"
      "Dylan Reference Manual: Inspector"
      "RFC-054 Terminal Interface Conventions"))))
