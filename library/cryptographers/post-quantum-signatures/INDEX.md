# Post-Quantum Cryptography and Signatures

This collection contains foundational papers and standards for cryptographic systems designed to resist attacks from quantum computers. As Shor's algorithm can break RSA and Diffie-Hellman on quantum computers, these systems provide quantum-resistant alternatives based on hash functions and lattice problems.

## Why Post-Quantum Cryptography?

When large-scale quantum computers become available, they will break current public-key cryptography:
- **Shor's algorithm** (1994) breaks RSA, Diffie-Hellman, and elliptic curve cryptography in polynomial time
- **Grover's algorithm** (1996) weakens symmetric crypto (but doesn't break it completely)

Post-quantum cryptography provides alternatives based on mathematical problems believed to be hard even for quantum computers.

## NIST Standards (2024)

### nist-fips-203-ml-kem-2024.pdf
**FIPS 203: Module-Lattice-Based Key-Encapsulation Mechanism Standard**
- Finalized August 2024
- ML-KEM (derived from CRYSTALS-KYBER)
- Quantum-resistant key establishment
- Based on lattice cryptography (Module Learning With Errors)
- Replaces Diffie-Hellman for key exchange in the quantum era

### nist-fips-204-ml-dsa-2024.pdf
**FIPS 204: Module-Lattice-Based Digital Signature Standard**
- Finalized August 2024
- ML-DSA (derived from CRYSTALS-Dilithium)
- Quantum-resistant digital signatures
- Based on lattice cryptography
- Replaces RSA/ECDSA signatures in the quantum era

### nist-fips-205-slh-dsa-2024.pdf
**FIPS 205: Stateless Hash-Based Digital Signature Standard**
- Finalized August 2024
- SLH-DSA (derived from SPHINCS+)
- Quantum-resistant signatures using only hash functions
- **Conservative choice**: security based solely on hash function properties
- Larger signatures but highest confidence in quantum resistance
- **Merkle's mathematics wins in the quantum era**

## Hash-Based Signatures (Merkle's Legacy)

### hash-based-signatures-overview-2023.pdf
**An Overview of Hash Based Signatures** (IACR ePrint 2023/411)
- Comprehensive technical overview of SPHINCS+ and XMSS
- Explains how Merkle trees provide quantum-resistant signatures
- Forward-secure signature schemes
- Connection to Merkle's 1979 certified digital signature work

### sphincs-practical-stateless-2015.pdf
**SPHINCS: Practical Stateless Hash-Based Signatures**
- NIST Post-Quantum Cryptography Workshop 2015
- Original SPHINCS design (evolved into SPHINCS+)
- Stateless variant of hash-based signatures
- No need to maintain state between signatures (unlike XMSS)
- Foundation for NIST FIPS 205

### hash-based-signatures-nist-2015.pdf
**Hash-based Signatures: An Outline for a New Standard**
- NIST Post-Quantum Workshop 2015
- Roadmap for standardizing hash-based signatures
- XMSS (eXtended Merkle Signature Scheme)
- Led to NIST SP 800-208 (XMSS standard)

### stateless-hash-signatures-2025.pdf
**Stateless Hash-Based Signatures for Post-Quantum Security Keys** (IACR ePrint 2025/298)
- Latest research (January 2025)
- Optimizing SPHINCS+ for embedded systems
- Performance improvements for hardware security keys
- Shows hash-based signatures are practical even in constrained environments

## Lattice-Based Cryptography Foundations

### regev-learning-with-errors-2009.pdf
**On Lattices, Learning with Errors, Random Linear Codes, and Cryptography**
- Oded Regev, Journal of the ACM, 2009 (originally STOC 2005)
- **THE FOUNDATIONAL PAPER** for modern lattice-based cryptography
- Introduces Learning With Errors (LWE) problem
- Shows worst-case to average-case reduction for lattice problems
- Quantum reduction from lattice problems to LWE
- Basis for CRYSTALS-KYBER (FIPS 203) and CRYSTALS-Dilithium (FIPS 204)

### ntru-ring-based-cryptosystem-1998.pdf
**NTRU: A Ring-Based Public Key Cryptosystem**
- Hoffstein, Pipher, Silverman, ANTS 1998
- **First practical lattice-based cryptosystem** (predates LWE by 7 years)
- Based on polynomial rings and lattice problems
- Fast operations, compact keys
- Influenced modern lattice cryptography
- Variant submitted to NIST PQC competition

## Historical Context

1. **1979**: Ralph Merkle invents hash trees and hash-based signatures
2. **1996**: Grover's algorithm shows quantum computers can speed up search
3. **1997**: Shor's algorithm threatens RSA and Diffie-Hellman
4. **1998**: NTRU - first practical lattice-based crypto
5. **2005/2009**: Regev's LWE - foundation for modern lattice crypto
6. **2015**: SPHINCS and XMSS - practical hash-based signatures
7. **2024**: NIST finalizes post-quantum standards (FIPS 203, 204, 205)
8. **2025**: Active deployment and optimization ongoing

## The Merkle Connection

Ralph Merkle's 1979 work on hash trees directly leads to modern quantum-resistant signatures:
- XMSS uses Merkle trees with authentication paths
- SPHINCS+ uses hyper-trees (trees of Merkle trees)
- FIPS 205 (SLH-DSA) standardizes Merkle's mathematical approach

**In the quantum era, Merkle's mathematics endures while number-theory-based crypto falls.**

## Sources

Papers obtained from:
- NIST Computer Security Resource Center: https://csrc.nist.gov/
- IACR ePrint Archive: https://eprint.iacr.org/
- arXiv: https://arxiv.org/
- Official NTRU website: https://www.ntru.org/
- Oded Regev's academic page: https://cims.nyu.edu/~regev/
