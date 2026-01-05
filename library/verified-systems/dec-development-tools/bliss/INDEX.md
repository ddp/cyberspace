# BLISS: DEC's Systems Programming Language

This collection contains documentation for BLISS (Basic Language for Implementation of System Software), the language used to implement much of DEC's VMS operating system and layered products.

## What is BLISS?

**BLISS** = Basic Language for Implementation of System Software

**Origin:**
- Invented by **William A. Wulf** at Carnegie Mellon University (CMU) in **1969**
- Originally for the DEC PDP-10
- Adopted by Digital Equipment Corporation in **1975**
- Became DEC's primary systems implementation language

**Purpose:**
High-performance systems programming with machine independence and strong optimization capabilities.

**Used To Implement:**
- **VAX/VMS Operating System** (large portions)
- **RSX-11M** (PDP-11 operating system)
- **Network protocols** (DECnet, LAT)
- **Compilers and tools** (some DECset components)
- **Device drivers**
- **Firmware**

## The Papers and Documentation

### bliss-systems-programming-wulf-1971.pdf
**BLISS: A Language for Systems Programming**
- W.A. Wulf, D.B. Russell, A.N. Habermann
- Carnegie Mellon University, 1971
- **THE ORIGINAL PAPER**

**Design Goals:**
1. **Machine independence**: Write once, run on multiple architectures
2. **Efficiency**: Generate code as good as hand-written assembly
3. **Control**: Low-level access when needed
4. **Readability**: Clearer than assembly, terser than ALGOL

**Revolutionary Features (for 1970):**

**1. Expressions, Not Statements:**
- Everything is an expression (returns a value)
- `IF x THEN y ELSE z` is an expression
- Assignment returns the assigned value
- Enables complex one-liners

**2. Explicit Fetch Operator (. prefix):**
```bliss
X = 5;        ! Assign 5 to location X
.X            ! Fetch value at location X
X = .Y;       ! Assign value of Y to X
X = Y;        ! Assign ADDRESS of Y to X (pointer assignment)
```

**Why?** Makes pointer operations explicit, avoids hidden dereferences

**3. Structure Access:**
```bliss
STRUCTURE node [base, offset, size] =
    base<offset, size>;

! Access bitfield from base address
```

**4. No Type Checking:**
- BLISS is **typeless** (everything is a word/longword)
- Compiler doesn't enforce types
- Programmer responsible for correctness
- Enables low-level manipulation

**5. Powerful Macros:**
- Compile-time computation
- Code generation
- Domain-specific languages within BLISS

**6. Structure Attributes:**
- Precise control over data layout
- Bitfields, alignment, packing
- Essential for hardware registers

**Example BLISS Code:**
```bliss
MODULE example;

! Linked list node
STRUCTURE node =
    [LINK] : REF node,
    [DATA] : WORD;

ROUTINE insert(head, new_node) =
    BEGIN
    new_node[LINK] = .head;
    head = new_node;
    END;

END ELUDOM
```

**Comparison with C (1971):**
- BLISS predates C (which came in 1972)
- Both designed for systems programming
- C won due to Unix adoption
- BLISS more powerful but less portable

### bliss-language-history.pdf
**The BLISS Programming Language: A History**
- Ronald F. Brender (DEC compiler architect)
- Tufts University
- **COMPREHENSIVE HISTORY**

**The CMU Years (1969-1975):**
- Wulf develops BLISS for PDP-10
- Goal: Better than assembly, more efficient than ALGOL
- Research language for OS development

**DEC Adoption (1975):**
- DEC needed systems language for VAX
- BLISS-36 (PDP-10), BLISS-32 (VAX), BLISS-16 (PDP-11)
- Implemented VMS kernel and utilities

**Why DEC Chose BLISS:**
1. **Performance**: Generated excellent machine code
2. **Control**: Could access hardware directly
3. **Portability**: Same source for PDP-11, VAX, Alpha
4. **Proven**: Already used at CMU

**BLISS Variants:**
- **BLISS-10**: PDP-10 (original)
- **BLISS-11**: PDP-11 (16-bit)
- **BLISS-16**: PDP-11 (improved)
- **BLISS-32**: VAX (32-bit)
- **BLISS-64**: Alpha (64-bit)

**VMS and BLISS:**
- VMS kernel: Mix of BLISS-32 and VAX MACRO assembly
- Record Management Services (RMS): Mostly BLISS
- Network software: DECnet implemented in BLISS
- Utilities: Many CLI commands written in BLISS

**The Decline:**
- C became dominant in 1980s-1990s
- Unix standardized on C
- More C programmers than BLISS programmers
- DEC gradually shifted to C for new development

**Legacy:**
- VMS still contains millions of lines of BLISS
- OpenVMS maintained by VMS Software Inc. (VSI)
- BLISS compiler still available (part of OpenVMS SDK)
- Historical importance in compiler optimization theory

### bliss-language-reference-manual.pdf
**BLISS Language Reference Manual**
- VSI (VMS Software Inc.)
- Official language specification
- Covers BLISS-16, BLISS-32, BLISS-64

**Contents:**

**1. Language Elements:**
- Lexical structure (identifiers, literals, operators)
- Expressions and operators
- Control structures (IF, WHILE, SELECT, REPEAT)
- Routine declarations
- Module structure

**2. Data Structures:**
- STRUCTURE declarations
- REF (reference/pointer) types
- VECTOR and BLOCKVECTOR (arrays)
- Bitfield access

**3. Storage Allocation:**
- GLOBAL, LOCAL, OWN storage classes
- BIND (create alias for expression)
- REF allocation

**4. Macros:**
- Compile-time expansion
- Conditional compilation
- Code generation

**5. Linkage:**
- EXTERNAL declarations
- GLOBAL definitions
- PSECT (program section) control

**6. Machine-Specific:**
- BUILTIN functions (hardware instructions)
- Register allocation
- Calling conventions

**7. Compiler Directives:**
- Optimization controls
- Listing options
- Error reporting

**Advanced Features:**

**Coroutines:**
```bliss
ROUTINE coroutine =
    BEGIN
    COROUTINE main_routine;
    ! Cooperative multitasking
    END;
```

**Inline Assembly:**
```bliss
BUILTIN INSQUE, REMQUE;  ! VAX queue instructions
```

**Conditional Compilation:**
```bliss
%IF %VARIANT EQL 1 %THEN
    ! Debug code
%FI
```

## Why BLISS Was Special

### The Fetch Operator (.)

**The Problem (in most languages):**
- Variables automatically dereferenced
- Can't tell from code if something is pointer or value
- Leads to bugs in systems code

**BLISS Solution:**
```bliss
ROUTINE swap(a, b) =
    BEGIN
    LOCAL temp;
    temp = .a;      ! Fetch value AT a
    a = .b;         ! Store value FROM b AT a
    b = .temp;      ! Store temp AT b
    END;

! Call: swap(x, y)  passes ADDRESSES of x and y
```

**Comparison:**
```c
// C version
void swap(int *a, int *b) {
    int temp = *a;     // BLISS: .a
    *a = *b;           // BLISS: a = .b
    *b = temp;         // BLISS: b = .temp
}
// Call: swap(&x, &y)
```

**BLISS is more explicit**: `x` vs `.x` (address vs value)

### Structure Definitions

**Hardware Register Example:**
```bliss
STRUCTURE control_register [base] =
    [ENABLE] base<0,1>,          ! Bit 0: enable flag
    [MODE]   base<1,2>,          ! Bits 1-2: mode (0-3)
    [STATUS] base<3,4>,          ! Bits 3-6: status code
    [ADDR]   base<7,25>;         ! Bits 7-31: address

! Usage:
BIND device_csr = control_register[0x20001000];

IF .device_csr[ENABLE] THEN
    device_csr[MODE] = 2;
```

**Portable Across Architectures:**
- Same BLISS source compiles for PDP-11, VAX, Alpha
- Structure definitions adapt to word size
- Endianness handled by compiler

### Expression-Oriented Design

**Everything Returns a Value:**
```bliss
x = (IF .y GTR 10 THEN 20 ELSE 30);

count = (WHILE .i LSS 100 DO (i = .i + 1; 1) ELSE 0);

status = (SELECT .command OF
    SET [1]: enable();
    SET [2]: disable();
    TES: error_code);
```

**Benefits:**
- More compact code
- Easier to optimize
- Functional programming style (before it was popular)

## BLISS vs. Other Systems Languages

| Feature | BLISS | C | Assembly | Ada |
|---------|-------|---|----------|-----|
| **Type Safety** | None (typeless) | Weak | None | Very strong |
| **Portability** | High (w/ variants) | High | None | High |
| **Performance** | Excellent | Excellent | Best | Good |
| **Readability** | Moderate | Moderate | Poor | High |
| **Learning Curve** | Steep | Moderate | Very steep | Very steep |
| **Hardware Access** | Excellent | Good | Best | Limited |

**BLISS Advantages:**
- ✓ Explicit memory operations (fetch operator)
- ✓ Powerful macro system
- ✓ Expression-oriented
- ✓ Generated excellent code

**BLISS Disadvantages:**
- ✗ No type safety (programmer must be careful)
- ✗ Proprietary to DEC
- ✗ Small community
- ✗ Cryptic syntax for beginners

## BLISS in VMS Architecture

**VMS Components in BLISS:**

**Kernel:**
- Process scheduler
- Memory management
- I/O subsystem
- Lock manager

**RMS (Record Management System):**
- File access methods
- Sequential, relative, indexed files
- Record locking

**Network Layers:**
- DECnet protocol stack
- LAT (Local Area Transport)
- Network drivers

**Why BLISS for VMS?**
1. **Performance**: Kernel must be fast
2. **Control**: Direct hardware access needed
3. **Reliability**: Explicit operations reduce bugs
4. **Portability**: VMS ran on VAX, Alpha, Itanium (via porting)

## The Optimizer

**BLISS Optimizer Philosophy:**
- Language designed to be optimizable
- Minimal aliasing (fetch operator helps)
- Expression trees easy to optimize
- Register allocation hints

**Optimizations Performed:**
- Common subexpression elimination
- Loop invariant code motion
- Dead code elimination
- Inline expansion
- Register allocation
- Instruction scheduling

**Result:**
- BLISS often matched hand-coded assembly
- VMS performance competitive with Unix (written in C)

## BLISS Influence on Language Design

**Influenced:**
- **C**: Expression-oriented features
- **Rust**: Explicit borrowing (like fetch operator)
- **Zig**: Explicit allocation, comptime

**Novel Ideas:**
- Expression-based control flow (now in Rust, Scala, Kotlin)
- Compile-time computation (macros, now in Rust, Zig)
- Explicit fetch/store (now in systems languages)

## Historical Anecdotes

**"ELUDOM" (MODULE backwards):**
- BLISS modules end with `END ELUDOM`
- Wulf's sense of humor
- Like `END IF`, `END WHILE`, `END ELUDOM`

**The "." Controversy:**
- Many programmers found fetch operator confusing
- "Why isn't `x` the value?"
- Wulf: "Because explicit is safer for systems code"
- Debate continues today (Rust borrows this idea)

**VMS Written in BLISS:**
- Often cited as "proof BLISS works"
- VMS was extremely reliable (99.99%+ uptime common)
- But also: Did BLISS contribute to reliability?
- Answer: Probably yes (explicit operations reduce bugs)

## Modern Status

**BLISS Today:**
- Still maintained by VSI for OpenVMS
- Legacy code still in production
- No new projects use BLISS
- Historical interest for language designers

**OpenVMS Continues:**
- Now on x86-64 (VSI port)
- BLISS compiler ported to x86-64
- Millions of lines of BLISS still running

**Why BLISS Didn't Survive:**
- Unix won the OS wars → C became standard
- Proprietary language (DEC-only initially)
- C had larger ecosystem (compilers, libraries, tools)
- Typeless design fell out of favor (safety concerns)

## Lessons from BLISS

**What Worked:**
- Expression-oriented design
- Explicit memory operations
- Powerful compile-time features
- Optimization-friendly semantics

**What Didn't:**
- Proprietary language (vendor lock-in)
- No type safety (error-prone)
- Cryptic syntax (steep learning curve)
- Lack of standard library

**Modern Equivalents:**
- **Rust**: Expression-oriented + type safety + explicit borrowing
- **Zig**: Comptime + manual memory management + clarity
- **C++**: Templates (like BLISS macros) + performance

## Connection to DEC Ecosystem

**BLISS + Ada + C:**
- DEC supported all three for different purposes:
  - **BLISS**: OS kernel, low-level systems (see this collection)
  - **Ada**: High-reliability applications (see ../ada/)
  - **C**: Portable applications, Unix compatibility

**DECset Integration:**
- BLISS supported by LSE (Language-Sensitive Editor)
- SCA (Source Code Analyzer) understood BLISS
- CMS (Code Management System) for version control
- See ../decset/ for development tools

## Sources

Documentation obtained from:
- VSI (VMS Software Inc.): https://vmssoftware.com/
- Carnegie Mellon University archives
- Tufts University computer science archives
- University of Arizona CS course materials
- CiteSeerX and academic repositories

## Further Reading

For DEC's safe application language:
- ../ada/ - Ada programming language for high-integrity systems

For DEC development environment:
- ../decset/ - Integrated development tools (LSE, SCA, CMS, MMS)

For systems written in systems languages:
- ../sel4/ - Verified OS kernel (C, not BLISS, but similar domain)
- ../l4-microkernel/ - Minimal OS kernels (assembly and C)

For modern systems languages:
- Rust documentation (spiritual successor to BLISS ideas)
- Zig documentation (comptime, explicit operations)
