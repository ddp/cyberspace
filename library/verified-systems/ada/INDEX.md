# Ada: The DoD High-Integrity Programming Language

This collection contains documentation for Ada 83 (ANSI/MIL-STD-1815A) and VAX Ada, Digital Equipment Corporation's implementation for OpenVMS systems.

## What is Ada?

**Ada** is a structured, statically typed, imperative programming language designed for embedded and real-time systems where **reliability** and **long-term maintainability** are critical.

**Origin:**
- Commissioned by the **US Department of Defense** (DoD) in 1975
- Named after **Ada Lovelace** (first computer programmer, 1840s)
- Designed by **Jean Ichbiah** (CII Honeywell Bull, France)
- Standardized as **ANSI/MIL-STD-1815A** in 1983

**Goal:**
Replace the 450+ programming languages used across DoD with a single, safe, portable language for mission-critical systems.

## Why Ada Matters for High-Assurance Systems

**Design Principles:**
1. **Strong typing**: Type errors caught at compile time
2. **Explicit interfaces**: No hidden dependencies
3. **Modularity**: Package-based abstraction
4. **Concurrency**: Built-in tasking model
5. **Exception handling**: Structured error recovery
6. **Portability**: Strict standard, validated compilers

**Safety Features:**
- No implicit type conversions (prevents subtle bugs)
- Array bounds checked at runtime (prevents buffer overflows)
- No pointer arithmetic (prevents memory corruption)
- Deterministic execution (for real-time systems)
- Strong encapsulation (prevents unauthorized access)

## The Papers and Documentation

### ada-83-mil-std-1815a.pdf
**Reference Manual for the Ada Programming Language (ANSI/MIL-STD-1815A)**
- **THE OFFICIAL STANDARD** (February 17, 1983)
- Developed by CII Honeywell Bull, later Alsys
- Under contract to US Department of Defense
- ~18 MB comprehensive language specification

**Contents:**
1. **Introduction**: Language philosophy and design goals
2. **Lexical Elements**: Identifiers, literals, delimiters
3. **Declarations and Types**: Strong type system
4. **Names and Expressions**: Syntax and semantics
5. **Statements**: Control flow constructs
6. **Subprograms**: Procedures and functions
7. **Packages**: Modularity and encapsulation
8. **Visibility Rules**: Scope and information hiding
9. **Tasks**: Concurrent programming model
10. **Program Structure**: Compilation units and libraries
11. **Exceptions**: Error handling mechanism
12. **Generic Units**: Parametric polymorphism
13. **Representation Clauses**: Low-level control
14. **Input-Output**: Standard file I/O
15. **Annexes**: Predefined packages and grammar

**Key Language Features:**

**Strong Typing:**
```ada
type Temperature is range -273.15 .. 1_000_000.0;
type Celsius is new Temperature;  -- Distinct type
type Fahrenheit is new Temperature;  -- Different from Celsius

C : Celsius := 100.0;
F : Fahrenheit := F;  -- COMPILE ERROR: type mismatch
```

**Packages (Modularity):**
```ada
package Stack is
   procedure Push(Item : Integer);
   procedure Pop(Item : out Integer);
   function Is_Empty return Boolean;
private
   -- Implementation hidden
end Stack;
```

**Tasking (Concurrency):**
```ada
task body Controller is
begin
   loop
      select
         accept Start;
         -- Handle start command
      or
         accept Stop;
         exit;  -- Terminate task
      end select;
   end loop;
end Controller;
```

**Exception Handling:**
```ada
begin
   Open(File, "data.txt");
   Process(File);
exception
   when Name_Error =>
      Put_Line("File not found");
   when others =>
      Put_Line("Unexpected error");
end;
```

### ada-83-nist-fips-119.pdf
**FIPS PUB 119: Ada Programming Language**
- National Institute of Standards and Technology (NIST)
- Federal Information Processing Standard
- Mandated Ada for US government software projects
- Same content as MIL-STD-1815A (public domain version)

**Significance:**
- Made Ada a **federal standard** for government software
- Required Ada for defense contracts (1980s-1990s)
- Ensured compiler validation and portability
- Contributed to Ada's widespread adoption

### dec-ada-lrm.pdf
**DEC Ada Language Reference Manual**
- Digital Equipment Corporation
- Order Number: AA–PYZAB–TK (June 1995)
- References MIL-STD-1815A-1983
- DEC-specific implementation notes

**Coverage:**
- Conforms to ANSI/MIL-STD-1815A standard
- VAX and Alpha architecture specifics
- OpenVMS integration
- Performance characteristics
- Compiler pragmas and attributes

### vax-ada-developing-programs.pdf
**DEC Ada: Developing Ada Programs on OpenVMS Systems**
- Order Number: AA–PWGYA–TK
- Practical guide for Ada development on VAX/VMS
- Covers the full development lifecycle

**Contents:**
1. **Introduction to DEC Ada**: Tools and environment
2. **Program Development**: Edit-compile-debug cycle
3. **Ada Library Management**: Program library structure
4. **Compilation**: Compiler options and pragmas
5. **Linking**: Creating executables
6. **Debugging**: Using the OpenVMS debugger with Ada
7. **Performance**: Optimization techniques
8. **Integration**: Calling other languages (FORTRAN, C, BLISS)

**Development Tools Covered:**
- **ACS (Ada Compilation System)**: Compiler
- **Ada Library Manager**: Manages compilation units
- **OpenVMS Debugger**: Source-level debugging
- **VAXset Integration**: LSE, SCA, CMS, MMS (see ../dec-development-tools/decset/)

**Unique VAX Ada Features:**
- Direct interface to VMS system services
- Integration with VMS file system
- Support for VMS Record Management Services (RMS)
- Access to VMS mailboxes and event flags

### vax-ada-installation-guide.pdf
**DEC Ada Installation Guide for OpenVMS VAX Systems**
- Order Number: AA–EF85G–TE
- System manager documentation
- Installation and configuration procedures

**Contents:**
- Prerequisites and system requirements
- Installation procedures
- License management (LMF)
- System-wide configuration
- Troubleshooting

## Ada's Impact on Software Engineering

### Languages Influenced by Ada

**Direct Descendants:**
- **Ada 95** (1995): Object-oriented extensions, protected types
- **Ada 2005** (2005): Interfaces, limited withs, ravenscar profile
- **Ada 2012** (2012): Contracts (preconditions/postconditions), aspects
- **SPARK**: Verifiable subset of Ada for high-assurance systems

**Influenced Languages:**
- **C++**: Templates inspired by Ada generics
- **Java**: Packages, strong typing, exception handling
- **Eiffel**: Design by contract (inspired by Ada's type system)
- **Modula-2/Modula-3**: Module systems

### Real-World Ada Deployments

**Aerospace:**
- **Boeing 777**: Flight control systems
- **Airbus A320/A340/A380**: Primary flight software
- **Mars Curiosity Rover**: Autonomy software
- **Ariane 5 rocket**: Flight control (after famous 1996 exception bug!)
- **Space Shuttle**: Parts of flight software

**Defense:**
- **F-22 Raptor**: Avionics
- **Eurofighter Typhoon**: Mission computers
- **Patriot missile system**: Fire control
- **Aegis Combat System**: Naval warfare

**Transportation:**
- **Paris Metro Line 14**: Driverless train control (SPARK Ada)
- **London Tube**: Signaling systems
- **SNCF TGV**: High-speed train control
- **Air traffic control systems** worldwide

**Medical:**
- **Radiation therapy machines**: Safety-critical control
- **Infusion pumps**: Drug delivery systems

**Industrial:**
- **Nuclear power plant** control systems
- **Railway signaling**: European Train Control System (ETCS)

## Ada vs. Other Safety-Critical Languages

| Language | Type Safety | Concurrency | Verification | Adoption |
|----------|-------------|-------------|--------------|----------|
| **Ada** | Very strong | Built-in tasks | SPARK subset | Aerospace, defense |
| C | Weak | External (pthreads) | Difficult | Embedded, OS |
| C++ | Moderate | std::thread (C++11) | Moderate | Many domains |
| Rust | Very strong | Built-in | Growing | Systems, embedded |
| MISRA C | Moderate | Guidelines | Code analysis | Automotive |

**Ada Advantages:**
- ✓ Designed for safety from start
- ✓ Built-in concurrency (not bolted on)
- ✓ Decades of proven use
- ✓ SPARK verifiable subset
- ✓ Validated compilers (strict conformance)

**Ada Challenges:**
- ✗ Smaller developer community than C/C++
- ✗ Fewer third-party libraries
- ✗ Verbose syntax (explicit is safer but longer)
- ✗ Compiler availability (fewer vendors)

## SPARK: Verifiable Ada Subset

**SPARK** is a subset of Ada designed for formal verification:
- No dynamic memory allocation
- No recursion (bounded execution)
- No access types (no pointers)
- No exceptions (explicit error handling)
- Contracts (preconditions, postconditions, invariants)

**Verification:**
- **Static analysis**: Prove absence of runtime errors
- **Flow analysis**: Information flow security
- **Formal proof**: Verify functional correctness

**Tools:**
- **SPARK Pro**: Altran/AdaCore verification toolset
- **GNATprove**: Automated theorem prover
- **Why3**: Proof obligations generator

**Example SPARK Contract:**
```ada
procedure Swap(X, Y : in out Integer)
   with Post => X = Y'Old and Y = X'Old;
```

**Used For:**
- Tokeneer (secure login system, formally verified)
- MULTOS (smartcard OS)
- iFACTS (air traffic control, Lockheed Martin)

## The Ada Validation Process

**Compiler Validation:**
- Ada compilers must pass **ACVC** (Ada Compiler Validation Capability)
- Over 5,000 test cases
- Strict conformance to standard
- Certificate issued by Ada Validation Facility

**Benefits:**
- Guaranteed portability across validated compilers
- No vendor-specific dialects (unlike C compilers in 1980s)
- DoD mandated validated compilers only

## Historical Timeline

1. **1975**: DoD issues "Steelman" requirements for new language
2. **1977-1979**: Four teams compete (Red, Green, Blue, Yellow)
3. **1979**: **Green team (CII Honeywell Bull) selected**, language named Ada
4. **1980**: Ada 80 preliminary standard
5. **1983**: **Ada 83 (MIL-STD-1815A)** official standard
6. **1987**: ANSI standardizes Ada (ANSI/MIL-STD-1815A)
7. **1987**: ISO standardizes Ada (ISO 8652:1987)
8. **1995**: Ada 95 adds OOP (first ISO-standardized OO language!)
9. **1997**: GNAT (GNU Ada) becomes production-quality
10. **2000s**: DoD mandate relaxed (but Ada still widely used)
11. **2005**: Ada 2005 adds interfaces, Ravenscar profile
12. **2012**: Ada 2012 adds contracts (preconditions/postconditions)
13. **2020s**: Ada 2022 adds parallel constructs, image attributes

## DEC's Role in Ada Adoption

**VAX Ada:**
- One of the first commercial Ada compilers
- High-quality implementation
- Tight OpenVMS integration
- Used in many defense projects

**DEC's Ada Tools:**
- Integration with DECset (LSE, SCA, CMS)
- Debugger support
- Performance analysis tools
- Cross-language calling conventions

**Impact:**
- Made Ada practical for large projects
- Showed Ada could be efficient (dispelled "slow" myth)
- Contributed to Ada's success in defense sector

## Ada in the Modern Era

**Current Compilers:**
- **GNAT**: GNU Ada Translator (GPL, now maintained by AdaCore)
- **GNAT Pro**: Commercial support by AdaCore
- **Janus/Ada**: Native Windows compiler
- **ApexAda**: Embedded systems (legacy)

**Modern Uses:**
- **Safety-critical embedded**: Still the best choice
- **Railway systems**: CENELEC EN 50128 recommends Ada
- **Avionics**: DO-178C certified Ada compilers available
- **Security**: SPARK for high-assurance systems

**New Projects:**
- **Libadalang**: Ada parsing and analysis library
- **Alire**: Modern Ada package manager (like Cargo for Rust)
- **Ada Drivers Library**: Embedded HAL for ARM Cortex-M
- **GNAT for embedded**: Ravenscar runtime for bare-metal

## Why Ada Didn't Dominate

**Initial Challenges:**
- Mandated by DoD (resentment from developers)
- Early compilers were slow and buggy
- Complex language (steep learning curve)
- "Design by committee" perception

**What Happened:**
- C++ gained momentum in commercial sector
- Java promised "write once, run anywhere"
- Open source movement favored C
- DoD mandate ended (1997)

**But Ada Survived:**
- Niche in safety-critical systems
- Better than alternatives where reliability matters
- Proven track record in aerospace/defense
- SPARK adds formal verification capability

## Ada's Legacy

**Language Design:**
- Showed strong typing is practical
- Proved concurrency can be built-in
- Demonstrated importance of standardization
- Influenced modern safe languages (Rust, Go)

**Software Engineering:**
- Emphasized maintainability and readability
- Promoted modular design (packages)
- Validated compiler concept (no dialects)
- Design-by-contract (precursor to SPARK)

**Quote from Jean Ichbiah (Ada's designer):**
> "The price of reliability is the pursuit of the utmost simplicity. It is a price which the very rich find most hard to pay."

## Connection to Verified Systems

**Ada and Formal Verification:**
- seL4 kernel NOT written in Ada (see ../sel4/)
- But SPARK Ada is formally verifiable
- Different approach: Constrain language for provability
- CompCert could compile Ada (see ../coq/)

**The Verification Spectrum:**
```
Testing ----------- Static Analysis ----------- Formal Proof
   ↑                      ↑                          ↑
   C                    Ada 83                   SPARK Ada
   C++                  Rust                     seL4 (Isabelle)
                        MISRA C                  CompCert (Coq)
```

## Sources

Documentation obtained from:
- Russ Cox's archives: https://swtch.com/
- NIST Federal Information Processing Standards
- VMS Software Inc. (VSI): https://vmssoftware.com/
- Legacy DEC documentation archives
- AdaCore and Ada Resource Association

## Further Reading

For verified software and compilers:
- ../coq/ - CompCert verified compiler (could compile Ada)
- ../sel4/ - Formally verified OS kernel

For DEC development tools:
- ../dec-development-tools/decset/ - DECset CASE tools
- ../dec-development-tools/bliss/ - BLISS systems programming language

For modern safe systems languages:
- Rust (memory-safe C++ alternative)
- SPARK (formally verifiable Ada subset)
- Frama-C (C verification framework)
