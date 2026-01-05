# Quantum Algorithms and Cryptanalysis

This collection contains the foundational papers on quantum algorithms that threaten classical cryptography and drive the need for post-quantum cryptographic systems.

## The Quantum Threat to Cryptography

Quantum computers exploit quantum superposition and entanglement to solve certain problems exponentially faster than classical computers. Two algorithms in particular threaten modern cryptography:

1. **Shor's Algorithm** (1997) - Breaks RSA, Diffie-Hellman, and elliptic curve cryptography
2. **Grover's Algorithm** (1996) - Weakens symmetric crypto (requires doubling key sizes)

## Papers in This Collection

### shor-quantum-factoring-1997.pdf
**Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer**
- Peter Shor, SIAM Journal on Computing, 26(5):1484-1509, 1997
- arXiv: quant-ph/9508027

**Impact:**
- Shows integer factorization can be solved in polynomial time on a quantum computer
- Shows discrete logarithm problem can be solved in polynomial time
- **Breaks RSA encryption** (relies on factoring being hard)
- **Breaks Diffie-Hellman-Merkle key exchange** (relies on discrete log being hard)
- **Breaks elliptic curve cryptography** (relies on elliptic curve discrete log)

**Algorithm Complexity:**
- Classical factoring: Sub-exponential (GNFS ~2^O(n^1/3))
- Shor's algorithm: Polynomial O(n³) for n-bit integers
- This is an exponential speedup

**Quantum Requirements:**
- Requires ~2n qubits to factor an n-bit number
- Requires error-corrected quantum gates
- Estimated ~20 million noisy qubits needed to break RSA-2048
- Current quantum computers: ~1000 qubits (as of 2025)
- Timeline: Unknown, but serious threat within 10-20 years

**Historical Context:**
- Submitted to arXiv in 1995
- Published in SIAM Journal on Computing 1997
- Earned Shor the 2023 Breakthrough Prize in Mathematics
- Catalyzed the field of post-quantum cryptography

### grover-quantum-search-1996.pdf
**A Fast Quantum Mechanical Algorithm for Database Search**
- Lov K. Grover, Proceedings of STOC 1996
- arXiv: quant-ph/9605043

**Impact:**
- Shows unstructured search can be done in O(√N) time instead of O(N)
- **Weakens symmetric cryptography** (AES, ChaCha20, etc.)
- **Weakens hash functions** (SHA-2, SHA-3, etc.)
- Does NOT break symmetric crypto, just requires larger keys

**Algorithm Complexity:**
- Classical search: O(N) queries for unstructured search
- Grover's algorithm: O(√N) queries
- This is a quadratic speedup

**Practical Impact:**
- AES-128 → effectively 64-bit security (broken)
- AES-256 → effectively 128-bit security (adequate)
- SHA-256 → effectively 128-bit collision resistance (adequate)
- **Doubling key/hash sizes suffices** to maintain security

**Applications Beyond Cryptanalysis:**
- General speedup for NP-complete problems
- Database search and optimization
- Quantum machine learning
- Solving SAT problems

**Comparison:**

| Security Primitive | Classical Strength | Grover Attack | Recommendation |
|--------------------|-------------------|---------------|----------------|
| AES-128            | 128-bit           | 64-bit        | Use AES-256    |
| AES-256            | 256-bit           | 128-bit       | Adequate       |
| SHA-256            | 256-bit           | 128-bit       | Adequate       |
| SHA-512            | 512-bit           | 256-bit       | Conservative   |

## Why These Papers Matter

These two papers define the quantum threat landscape:

**Public-key crypto:** Completely broken by Shor's algorithm
- RSA: Broken
- Diffie-Hellman: Broken
- Elliptic curves: Broken
- **Solution:** Move to post-quantum cryptography (lattice-based, hash-based, code-based)

**Symmetric crypto:** Weakened by Grover's algorithm
- AES-128: Weakened to 64-bit effective security
- AES-256: Remains strong (128-bit effective)
- **Solution:** Use larger key sizes (256-bit minimum)

**Hash functions:** Weakened by Grover's algorithm
- Collision resistance halved
- Preimage resistance halved
- **Solution:** Use SHA-256 minimum (SHA-512 for conservative choice)

## The Quantum-Resistant Future

**What survives quantum attack:**
- Hash-based signatures (SPHINCS+, XMSS) - Based on Merkle's 1979 work
- Lattice-based crypto (CRYSTALS-KYBER, CRYSTALS-Dilithium) - Based on Regev's LWE
- Code-based crypto (Classic McEliece)
- Symmetric crypto with doubled key sizes (AES-256, ChaCha20-256)

**Merkle's mathematics endures** while number-theory-based crypto (RSA, DH, ECC) falls to Shor's algorithm.

## Timeline

- **1994**: Shor discovers factoring algorithm (published 1995/1997)
- **1996**: Grover discovers search algorithm
- **1997**: Formal publication of Shor's algorithm
- **2000s**: Post-quantum cryptography research intensifies
- **2016**: NIST begins post-quantum standardization process
- **2024**: NIST publishes FIPS 203, 204, 205 (quantum-resistant standards)
- **2025**: Active deployment of post-quantum cryptography
- **2030s?**: Large-scale quantum computers potentially available

## Sources

Papers obtained from:
- arXiv: https://arxiv.org/
- Peter Shor's MIT publications: https://math.mit.edu/~shor/elecpubs.html
- STOC proceedings archives
