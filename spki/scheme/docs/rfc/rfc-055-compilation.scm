(rfc
  (number 55)
  (title "Compilation and Type Inference Conventions")
  (section
    "Abstract"
    (p "This RFC specifies compilation conventions for Cyberspace Scheme modules: type declarations for tractable inference, build dependency levels, beta vs production flags, and the forge build system. The guiding principle is Ada's \"declare everything, infer nothing.\""))
  (section
    "1. The Inference Problem"
    (p "Whole-program type inference without declarations can exhibit exponential complexity. Chicken Scheme's scrutinizer with -strict-types performs flow-sensitive analysis that becomes intractable when:")
    (list
      "Functions contain many conditional branches with side effects"
      "Format strings (sprintf) create implicit polymorphic constraints"
      "Type information cannot flow through set! mutations")
    (p "A function with 30 conditional sprintf calls can take 5+ minutes to analyze. The same function with type declarations compiles in under 1 second."))
  (section
    "2. The Ada Principle"
    (p "Ada's compilation model requires explicit type declarations everywhere. The compiler is a checker, not a guesser. This trades verbosity for predictability.")
    (p "For Cyberspace modules, we adopt a hybrid approach:")
    (list
      "Functions with complex control flow MUST have type declarations"
      "Simple leaf functions MAY rely on inference"
      "Public API functions SHOULD have declarations for documentation")
    (code scheme ";; Required: complex function with many branches
(: session-summary (-> (list-of string)))
(define (session-summary) ...)

;; Optional: simple leaf function
(define (format-size bytes)
  (cond ...))"))
  (section
    "3. Type Declaration Patterns"
    (subsection
      "3.1 Import chicken.type"
      (p "Modules using type declarations must import the type system:")
      (code scheme "(import (chicken type))"))
    (subsection
      "3.2 Declaration Syntax"
      (p "Type declarations precede function definitions:")
      (code scheme "(: function-name (arg-type ... -> return-type))

;; Examples:
(: format-stat (symbol string string -> (or string false)))
(: session-uptime (-> fixnum))
(: goodbye (#!optional (or false procedure) -> noreturn))"))
    (subsection
      "3.3 Typed Helper Pattern"
      (p "Break large functions into small typed helpers:")
      (code scheme ";; BAD: One large function with 30 sprintf calls
(define (session-summary)
  (let ((stats '()))
    (when (> (session-stat 'reads) 0)
      (set! stats (cons (sprintf \"~a reads\" ...) stats)))
    ... ;; 29 more similar blocks
    (reverse stats)))

;; GOOD: Small typed helpers composed via filter
(: format-stat (symbol string string -> (or string false)))
(define (format-stat key singular plural-suffix)
  (let ((n (session-stat key)))
    (if (> n 0)
        (string-append (number->string n) \" \" singular
                       (if (= n 1) \"\" plural-suffix))
        #f)))

(define (session-summary)
  (filter identity
    (list (format-stat 'reads \"read\" \"s\")
          (format-stat 'writes \"write\" \"s\")
          ...)))")
      (p "Each helper is independently typed. The type checker analyzes them separately, avoiding combinatorial explosion.")))
  (section
    "4. Build Dependency Levels"
    (p "Modules are organized into dependency levels for parallel compilation. Modules within a level have no mutual dependencies and can build concurrently.")
    (code scheme ";; Level 0: No cyberspace dependencies
(\"os\" \"crypto-ffi\" \"sexp\" \"capability\")

;; Level 1: Single dependencies from Level 0
(\"mdns\" \"fips\" \"audit\" \"wordlist\" \"bloom\" \"catalog\" \"keyring\" \"portal\")

;; Level 2: Dependencies on Levels 0+1
(\"cert\" \"enroll\")

;; Level 3: Dependencies on Level 2
(\"gossip\" \"security\")

;; Level 4: Dependencies on Level 3
(\"vault\" \"auto-enroll\")

;; Level 5: Final layer
(\"ui\")")
    (p "Adding a new module requires analyzing its imports to determine the correct level. A module importing from level N must be placed in level N+1 or higher."))
  (section
    "5. Beta vs Production Builds"
    (subsection
      "5.1 Beta Mode"
      (p "During development and beta testing, enable strict type checking:")
      (code scheme "(define *beta-build* #t)

;; Results in: csc -shared -J -strict-types module.scm")
      (p "Benefits:")
      (list
        "Catches type errors at compile time"
        "Validates type declaration accuracy"
        "Identifies functions needing refactoring"))
    (subsection
      "5.2 Production Mode"
      (p "For release builds, disable strict checking for faster compilation:")
      (code scheme "(define *beta-build* #f)

;; Results in: csc -shared -J module.scm")
      (p "Type declarations remain as documentation but are not enforced.")))
  (section
    "6. The Forge Build System"
    (subsection
      "6.1 Forge Output"
      (p "The forge displays compilation status in boxes:")
      (code "+---------------- forge: portal ----------------+
| csc -shared -J -strict-types portal.scm      |
| > 241K + 677B import in 921ms                |
+----------------------------------------------+"))
    (subsection
      "6.2 Parallel Level Compilation"
      (p "Each dependency level compiles in parallel using process-fork. The build waits for all processes in a level before starting the next level.")
      (code scheme "(define (rebuild-level-parallel! modules-in-level)
  (let* ((pids (map (lambda (module)
                      (process-fork
                        (lambda ()
                          (rebuild-module! module)
                          (exit 0))))
                    modules-in-level)))
    (for-each process-wait pids)))"))
    (subsection
      "6.3 Rebuild Detection"
      (p "A module needs rebuilding when:")
      (list
        "The .so file is missing"
        "The .import.scm file is missing"
        "The source .scm is newer than the .so"
        "The architecture stamp doesn't match")))
  (section
    "7. Compiler Warnings"
    (p "With -strict-types, the scrutinizer reports:")
    (list
      "Type mismatches (argument types don't match declarations)"
      "Invalid arguments (e.g., passing #f where struct expected)"
      "Deprecated identifiers"
      "Format string errors")
    (p "All warnings should be addressed. A warning-free build indicates type-safe code.")
    (code ";; Example warning:
Warning: Invalid argument
  In procedure `discover-and-elect',
  Argument #1 to procedure `tcp-accept' has an invalid type:
    false
  The expected type is:
    (struct tcp-listener)"))
  (section
    "8. Performance Expectations"
    (table
      (header "Module Size" "Without Types" "With Types" "With Declarations")
      (row "Small (<500 LOC)" "~500ms" "~700ms" "~700ms")
      (row "Medium (500-2000 LOC)" "~1s" "~2s" "~2s")
      (row "Large (>2000 LOC)" "~2s" "exponential*" "~7s"))
    (p "* Without type declarations, large modules with complex control flow can take minutes or fail to complete."))
  (section
    "9. References"
    (list
      "Chicken Scheme User's Manual: Types"
      "RFC-054 Terminal Interface Conventions (forge display)"
      "Ada Reference Manual: Type Declarations"
      "Hindley-Milner Type Inference (theoretical background)")))
