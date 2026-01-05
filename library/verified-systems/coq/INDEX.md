# Coq: The Calculus of Constructions and Verified Software

This collection contains foundational papers on the Coq theorem prover and its most famous application: CompCert, the first verified optimizing C compiler.

## What is Coq?

**Coq** is an interactive theorem prover based on the Calculus of Constructions (CoC), a type theory that unifies logic and computation. It allows mathematicians and computer scientists to:
- Write formal specifications
- Develop machine-checked proofs
- Extract verified programs from proofs

**Key Features:**
- **Curry-Howard Correspondence**: Proofs are programs, programs are proofs
- **Dependent Types**: Types can depend on values
- **Tactics Language**: Automated proof strategies
- **Extraction**: Generate OCaml/Haskell code from proofs

## The Papers

### coquand-huet-calculus-of-constructions-1986.pdf
**The Calculus of Constructions**
- Thierry Coquand and Gérard Huet
- INRIA (French National Institute for Research in Computer Science)
- 1986
- **THE THEORETICAL FOUNDATION**

**What Is the Calculus of Constructions?**
- A type theory that unifies:
  - **Propositional logic** (true/false statements)
  - **Predicate logic** (∀, ∃ quantifiers)
  - **Higher-order logic** (functions on functions)
  - **Typed λ-calculus** (functional programming)

**The Key Insight:**
> "Propositions are types, proofs are programs"

**Example:**
```
Proposition: ∀x, x + 0 = x
Type:        ∀x:ℕ, (x + 0 = x)
Proof:       λx. <proof term>
Program:     Function that constructs proof for any x
```

**Dependent Types:**
- Types can depend on values
- Example: `Vector(n)` = vector of length n
- Type system prevents out-of-bounds access at compile time

**Historical Context:**
- Extends work by Per Martin-Löf (intuitionistic type theory)
- Basis for Coq theorem prover (name honors Thierry Coquand)
- Influenced Agda, Lean, Idris proof assistants

**Applications:**
- Formal mathematics (Four Color Theorem proof)
- Software verification (CompCert compiler)
- Hardware verification (microprocessor designs)
- Cryptographic protocol proofs

### compcert-leroy-2009.pdf
**Formal Verification of a Realistic Compiler**
- Xavier Leroy, INRIA
- Communications of the ACM, July 2009
- **THE VERIFIED COMPILER BREAKTHROUGH**

**The Compiler Correctness Problem:**
- Compilers have bugs
- Optimizations introduce errors
- Safety-critical code may be miscompiled
- Testing is incomplete

**CompCert's Solution:**
- Prove the compiler correct using Coq
- **Guarantee**: Compiled code behaves exactly as source code
- **Coverage**: Entire compilation pipeline verified

**What's Verified:**
- C source code → Assembly language
- 8 compilation passes:
  1. Parsing and elaboration
  2. Simplification of control structures
  3. Translation to 3-address code (RTL)
  4. Register allocation
  5. Linearization
  6. Assembly generation

**Proof:**
- **52,000 lines of Coq proof**
- Proves: If source program has behavior B, compiled program has behavior B
- Covers all optimizations (constant folding, CSE, inlining, etc.)

**The Guarantee:**
```
Source Program (C)
    ↓
CompCert Compiler (verified)
    ↓
Assembly Code
    ↓
Guarantee: Assembly behaves like C
            (or compiler reports error)
```

**Real-World Testing:**
- Tested with Csmith random C generator
- **Zero miscompilations** found in verified portions
- Contrast: GCC and LLVM had hundreds of bugs

**Performance:**
- Generated code quality: ~90% of GCC -O1
- Not as fast as GCC -O3, but *provably correct*
- Acceptable for safety-critical systems

**Use Cases:**
- Aerospace: Airbus A380 flight control software
- Automotive: Safety-critical ECU code
- Medical: FDA-certifiable device software
- Nuclear: Reactor control systems

**Limitations:**
- Only covers a subset of C (no C++ features)
- Some optimizations not verified (use unverified passes)
- Assumes correct hardware and OS

## The Curry-Howard Correspondence

**The Big Idea:**
Proofs and programs are the same thing!

| Logic | Type Theory | Programming |
|-------|-------------|-------------|
| Proposition P | Type P | Specification |
| Proof of P | Term of type P | Implementation |
| P → Q | Function P → Q | Implication |
| P ∧ Q | Pair (P, Q) | Conjunction |
| P ∨ Q | Sum P + Q | Disjunction |
| ∀x. P(x) | Π-type | Universal quantification |
| ∃x. P(x) | Σ-type | Existential quantification |

**Example:**
- **Logic**: "If P then Q"
- **Type Theory**: Function from P to Q
- **Program**: `f : P → Q` implemented as `λx. ...`

## Why Coq Matters for Verified Systems

**Proof Automation:**
- Tactics language for automated proof search
- Discharge trivial subgoals automatically
- Human focuses on hard proof steps

**Extraction:**
- Coq proofs can be extracted to OCaml or Haskell
- Get verified programs from constructive proofs
- CompCert compiler extracted this way

**Large-Scale Verification:**
- Coq scaled to verify:
  - 52,000 line compiler (CompCert)
  - Four Color Theorem (mathematical proof)
  - Feit-Thompson Theorem (mathematical proof)
  - Cryptographic libraries (VST Verifiable C)

## Historical Timeline

1. **1972**: Per Martin-Löf develops intuitionistic type theory
2. **1984**: Thierry Coquand develops Calculus of Constructions
3. **1986**: Coquand & Huet publish CoC paper
4. **1989**: First version of Coq released (INRIA)
5. **2004**: Georges Gonthier uses Coq for Four Color Theorem
6. **2006**: CompCert project begins (Xavier Leroy)
7. **2009**: CompCert verification complete
8. **2012**: Feit-Thompson theorem verified in Coq
9. **2020s**: Coq used in industry (verified crypto, smart contracts)

## Comparison with Other Proof Assistants

| System | Logic | Language | Use Case |
|--------|-------|----------|----------|
| **Coq** | CoC | Gallina + Ltac | General purpose, software verification |
| Isabelle/HOL | HOL | ML | Used for seL4 kernel verification |
| Agda | Martin-Löf | Agda | Research, type theory exploration |
| Lean | CIC | Lean | Mathematics formalization, interactive |
| ACL2 | First-order | Lisp | Hardware verification, industrial |

## Major Verified Projects Using Coq

**CompCert** (2009):
- Verified C compiler
- 52,000 lines of Coq
- Used in safety-critical systems

**VST (Verifiable Software Toolchain)**:
- Verify C programs using Coq
- Separation logic for pointers
- Cryptographic libraries verified

**CertiKOS** (2016):
- Verified concurrent OS kernel
- Yale University
- Proves security and correctness

**Fiat Cryptography** (2017):
- Verified cryptographic primitives
- Used in BoringSSL (Google)
- Synthesizes correct-by-construction crypto code

**MirageOS**:
- Verified unikernel components
- OCaml extracted from Coq proofs
- Secure network services

## The Proof Burden

**CompCert Statistics:**
- C compiler: ~42,000 lines of Coq code
- Proofs: ~52,000 lines of Coq proof scripts
- Ratio: ~1.2:1 proof-to-code (better than seL4's 20:1!)

**Why Is CompCert's Ratio Better?**
- Compiler correctness is compositional (prove each pass)
- seL4 has complex concurrency and state machine
- Different domains have different proof difficulties

## Connection to Other Verified Systems

**The Verified Stack Vision:**
```
Verified Applications (Coq/Fiat)
    ↓
Verified Libraries (VST)
    ↓
Verified Compiler (CompCert)
    ↓
Verified OS (seL4, CertiKOS)
    ↓
Verified Hardware (RISC-V efforts)
```

**Current State:**
- seL4: Kernel verified (see ../sel4/)
- CompCert: Compiler verified ✓
- VST: C verification tool ✓
- Hardware: Partial (specific processors)
- Applications: Case-by-case

## Coq's Impact on Programming Languages

**Languages Influenced by Coq/CoC:**
- **Agda**: Pure dependent types
- **Idris**: Practical dependent types
- **Lean**: Interactive theorem proving + math
- **F***: Verification-oriented (Microsoft)
- **Dafny**: Auto-active verification

**Features Spreading to Mainstream:**
- Dependent types (limited forms)
- Refinement types (TypeScript, Flow)
- Proof-carrying code
- Smart contract verification (Solidity → Coq)

## Learning Resources

**Official Documentation:**
- Software Foundations (online textbook)
- Certified Programming with Dependent Types (CPDT)
- Coq Reference Manual

**Tools:**
- CoqIDE: Integrated development environment
- Proof General: Emacs interface
- VSCoq: VS Code extension
- jsCoq: Coq in the browser

## Why This Matters

**Before CompCert:**
> "We hope our compiler is correct, we tested it a lot."

**After CompCert:**
> "We *proved* our compiler is correct, miscompilation is impossible."

**Impact:**
- Shifts verification burden from testing to proving
- Enables certification of safety-critical systems
- Demonstrates formal methods can scale to real software

**Quote from Xavier Leroy:**
> "The striking thing about formal proof is that it's not about finding bugs (though it does), it's about the *confidence* that there are no bugs left to find."

## Sources

Papers obtained from:
- INRIA Research Reports: https://www.inria.fr/
- Xavier Leroy's publications: https://xavierleroy.org/
- Communications of the ACM: https://cacm.acm.org/
- Semantic Scholar and academic repositories

## Further Reading

For systems verified using Coq's proof techniques:
- ../sel4/ - Verified OS kernel (uses Isabelle, similar to Coq)
- ../l4-microkernel/ - Unverified predecessor to seL4
- ../trusted-mach/ - Early work on secure microkernels

For safety-critical programming language:
- ../ada/ - Ada language designed for high-assurance systems (once we add it!)
