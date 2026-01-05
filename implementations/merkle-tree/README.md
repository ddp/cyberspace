# Merkle Trees: Content-Addressable Storage

**Practical implementation of Ralph Merkle's 1979 authenticated data structures**

From the paper: *"A Certified Digital Signature"*
Source: `~/cyberspace/library/cryptographers/merkle/merkle-secrecy-authentication-public-key-1979.pdf`

## The Concept

Merkle trees provide **a single hash that authenticates an entire dataset** through a tree structure:

```
                    ROOT
                   /    \
                  /      \
              H(A+B)    H(C+D)
              /  \      /  \
             /    \    /    \
          H(A)  H(B) H(C)  H(D)
           |     |    |     |
          [A]   [B]  [C]   [D]  ← Original data
```

**Key Properties:**
- ✓ **Single root hash** authenticates entire dataset
- ✓ **Inclusion proofs** verify membership with O(log n) hashes
- ✓ **Content-addressable**: Hash identifies content uniquely
- ✓ **Tamper-evident**: Any change propagates to root

## Quick Start

```bash
# Build a Merkle tree from data items
./merkle.scm build "alice" "bob" "carol" "dave"

# Generate and verify an inclusion proof
./merkle.scm prove "bob" "alice" "bob" "carol" "dave"

# Store file by content hash (Git-like)
./merkle.scm store README.md

# Retrieve by hash
./merkle.scm retrieve <hash>

# Create a commit snapshot
./merkle.scm commit "Initial commit" file1.txt file2.txt
```

## How It Works

### 1. Tree Construction

Build a **binary tree** where each parent's hash combines its children:

```scheme
; Leaf nodes: hash of data
(define leaf-alice (make-leaf "alice"))
→ (leaf "f15a1d2a..." "alice")

; Internal nodes: hash of concatenated child hashes
(define parent (make-internal leaf-alice leaf-bob))
→ (internal "c11fa2e6..." leaf-alice leaf-bob)

; Root authenticates everything
root-hash = H(H(alice)+H(bob), H(carol)+H(dave))
```

**Example output:**
```
╔═══════════════════════════════════════
║ Merkle Tree Built
╠═══════════════════════════════════════
║ Items: 4
║ Leaves: 4
║ Height: 2
║ Root: be2b804df4554afd34fb2dcf0ab487ada6e6e491947186debd266f4ccd7c532f
╚═══════════════════════════════════════

Tree Structure:
NODE: be2b804d...
  NODE: c11fa2e6...
    LEAF: f15a1d2a... [alice]
    LEAF: bbea6855... [bob]
  NODE: aad64f52...
    LEAF: 9274c339... [carol]
    LEAF: 02bf5cda... [dave]
```

### 2. Inclusion Proofs

Prove an item exists in the tree with **O(log n) hashes**:

```
Proving "bob" is in tree:

Step 1: bob's parent = H(alice + bob)
  Need: alice's hash (sibling)

Step 2: root = H(bob's-parent + carol-dave-parent)
  Need: carol-dave-parent hash (sibling)

Proof = [alice-hash, carol-dave-parent-hash]
Verification: Recompute root from leaf using proof hashes
```

**Example output:**
```
✓ Inclusion Proof Found!
Proof path (2 steps):

  1. right sibling: f15a1d2abc339a70...
  2. left sibling: aad64f52a40da2d0...

✓ Proof verification PASSED
```

**Security:** Even if attacker captures proof, they can't:
- Prove false data is in tree (hash collision required)
- Forge proofs for data not in tree (would need to invert hash)
- Modify data without changing root (tamper-evident)

### 3. Content-Addressable Storage

Store data by its **content hash** (like Git):

```bash
$ ./merkle.scm store notes.txt
Stored: notes.txt
Hash: 72e0984c5e00d2c14da6243abfb5b1b9b9241eee691c7aa3a0c75b479afdcaea
Size: 19 bytes

$ ./merkle.scm retrieve 72e0984c...
Retrieved object:
─────────────────────────────────────
Hello, Cyberspace!
─────────────────────────────────────
```

**Properties:**
- Deduplication: Same content = same hash
- Immutability: Hash changes if content changes
- Verifiability: Can prove content matches hash

### 4. Git-Like Commits

Create **snapshots** of multiple files:

```bash
$ ./merkle.scm commit "Initial commit" file1.txt file2.txt
Commit 49dcd935b231e3142ff88b46a53f49c375c548ec3f7de8e51d3c3399b27c4be5
Tree d131f24d93947a711a788825b64d5ed50b6311527f194b435748606684714585
Files: 2

$ ./merkle.scm retrieve 49dcd935...
tree d131f24d...
message Initial commit
files 2
file1.txt dd5255c942ea25ebb76442627a00480890340775a3c6a5b8140eb5d2aab7991d
file2.txt 5af6656594fb1c42eea4670f06f1cfe84cd4ab36da530ccd5c0428daa5043047
```

The commit object stores:
- Tree hash (Merkle root of all files)
- Commit message
- File list with their content hashes

## Real-World Applications

### Git (2005)

Git uses Merkle trees extensively:

```
commit → tree → blob
         tree → blob
               blob
```

- **Blobs**: File contents (leaves)
- **Trees**: Directory listings (internal nodes)
- **Commits**: Snapshots with metadata (root + metadata)

**Same properties:**
- Content-addressable (objects stored by SHA-1 hash)
- Immutable (hash changes if content changes)
- Efficient verification (git fsck uses Merkle properties)

### Bitcoin (2009)

Blocks contain **Merkle tree of transactions**:

```
Block Header
├── Previous Block Hash
├── Merkle Root  ← Single hash of all transactions
└── Nonce

Merkle Tree:
        ROOT
       /    \
   H(T1+T2) H(T3+T4)
    /  \     /  \
  H(T1) H(T2) H(T3) H(T4)
   |     |     |     |
  [T1]  [T2]  [T3]  [T4]  ← Transactions
```

**Why Merkle trees?**
- Lightweight clients (SPV) can verify transactions with O(log n) proof
- Don't need to download entire blockchain
- Proof size: ~32 bytes × log₂(transactions)

### IPFS (2014)

**InterPlanetary File System** uses Merkle DAGs:

```
ipfs://QmHash  ← Content-addressed by Merkle root

Directory (Merkle node)
├── file1.txt → QmFile1Hash
├── file2.txt → QmFile2Hash
└── subdir/ → QmSubdirHash
```

**Properties:**
- Deduplication: Same file = same hash across network
- Verifiability: Download from any peer, verify with hash
- Immutability: Content changes = new hash (versioning)

### Certificate Transparency (2013)

Google's **append-only log** of TLS certificates:

```
Merkle Tree of Certificates
             ROOT (Signed Timestamp)
            /                    \
      STH(0-1000)            STH(1001-2000)
       /      \                 /      \
   Cert1    Cert2          Cert1001  Cert1002
```

**Why?**
- Prove certificate was logged (inclusion proof)
- Prove log hasn't been tampered with (consistency proof)
- Detect rogue certificates (monitors watch log)

## Performance

### Space Efficiency

For **n** data items:
- Tree nodes: ~2n-1 (n leaves + n-1 internal nodes)
- Storage: O(n) hashes
- Proof size: O(log n) hashes per item

**Example:** 1 million items
- Tree: ~2 million nodes
- Proof: ~20 hashes (log₂ 1,000,000 ≈ 20)
- Proof size: 20 × 32 bytes = 640 bytes

### Time Complexity

| Operation | Complexity | Example (1M items) |
|-----------|------------|-------------------|
| Build tree | O(n) | 1M hashes |
| Generate proof | O(log n) | 20 hash lookups |
| Verify proof | O(log n) | 20 hash computations |
| Update leaf | O(log n) | 20 hash recomputations |

### Build Performance

On modern hardware (tested):
- 4 items: <0.1s
- 100 items: ~1s
- 1000 items: ~10s

**Bottleneck:** SHA-256 computation via OpenSSL subprocess
**Optimization:** Use native hash library (libsodium, OpenSSL FFI)

## Security Properties

### ✓ Guarantees

**1. Tamper Detection**
```
Original tree root: abc123...
Attacker modifies leaf: "alice" → "ALICE"
New leaf hash changes → parent changes → root changes
Result: Root mismatch detected!
```

**2. Non-Repudiation**
```
Server publishes root hash: def456...
Client requests inclusion proof for item X
Server can't deny X exists (proof verifies against published root)
Server can't claim false data exists (can't forge proof)
```

**3. Efficient Verification**
```
Download 1GB dataset from untrusted source
Verify with: root hash + log(n) proof hashes
Don't need to trust source, only need trusted root hash
```

### ✗ Limitations

**1. No Protection Against Targeted Forgery of Root**
```
If attacker controls root hash publication:
  Can build alternate tree with different data
  Honest users need trusted source for root hash
```

**2. No Privacy**
```
Inclusion proofs reveal:
  - Sibling hashes at each level
  - Approximate position in tree (from path)
Not suitable for private data without encryption
```

**3. Append-Only (Without Additional Structure)**
```
Modifying leaf requires:
  - Recomputing O(log n) parent hashes
  - Publishing new root hash
  - Clients must track latest root
Need additional mechanisms for mutable structures
```

## Comparison to Other Structures

| Property | Merkle Tree | Hash List | Signed List |
|----------|-------------|-----------|-------------|
| Proof size | O(log n) | O(n) | O(1) |
| Proof generation | O(log n) | O(n) | O(1) |
| Tamper evident | ✓ | ✓ | ✓ |
| Efficient partial verification | ✓ | ✗ | ✗ |
| Append complexity | O(log n) | O(1) | O(1) |

**When to use Merkle trees:**
- Large datasets with partial verification needs
- Distributed systems (need to verify without full dataset)
- Need efficient inclusion/exclusion proofs

**When to use simpler alternatives:**
- Small datasets (hash list simpler)
- Always verify complete dataset (single hash sufficient)
- Trusted server (signatures may suffice)

## Extensions & Variations

### 1. Merkle Patricia Trie (Ethereum)

Combines Merkle tree + trie for **key-value storage**:
```
Root
├── 0x0... (accounts starting with 0)
├── 0x1... (accounts starting with 1)
...
└── 0xf... (accounts starting with f)
```

**Properties:**
- O(log n) proofs like Merkle trees
- Efficient updates (only affected branches)
- Key-based lookups

### 2. Sparse Merkle Trees

For **large address spaces** with few entries:
```
2²⁵⁶ possible leaves (one per hash)
Only store non-empty branches
Prove non-existence (path leads to empty node)
```

**Use case:** Ethereum state (2¹⁶⁰ possible addresses)

### 3. Merkle Mountain Ranges

For **append-only logs** without rebalancing:
```
Mountain range of perfect binary trees:
    /\       /\      /\
   /  \     /  \    /  \
  /    \   /    \  /\  /\
 [1-4] [5-8]  [9-12] [13-14]
```

**Benefit:** No rebalancing on append (O(1) amortized)

## Implementation Notes

### Hash Function

Uses **SHA-256** via OpenSSL:
```bash
echo -n "data" | openssl dgst -sha256 -hex
```

**Why SHA-256?**
- Cryptographically secure (collision-resistant)
- Widely available
- 256 bits = good security/size tradeoff
- Used by Bitcoin, Git (SHA-1→SHA-256 migration)

**Merkle's original paper** used DES in a one-way mode. Modern implementations use SHA-2 or SHA-3 family.

### Tree Structure

Represented as nested Scheme lists:
```scheme
(node-type hash left right)

Leaf:     (leaf "abc123..." "data" #f)
Internal: (internal "def456..." left-child right-child)
```

**Alternative representations:**
- Flat array (heap property: parent at i/2)
- Hash table (hash → node)
- Database (SQL: id, parent_id, hash, data)

### Odd Number of Leaves

When pairing nodes, if odd number:
```scheme
(define (pair-nodes nodes)
  (if (null? (cdr nodes))
      (list (make-internal (car nodes) (car nodes)))  ; Duplicate last
      ...))
```

**Alternatives:**
- Leave unpaired (unbalanced tree)
- Pad with empty hash
- Promote to parent level

**Bitcoin uses:** Duplicate last transaction if odd

## Educational Value

This implementation demonstrates:

**1. Cryptographic Properties**
- One-way hash functions
- Collision resistance
- Avalanche effect (small change → big hash difference)

**2. Data Structures**
- Binary trees
- Recursive algorithms
- Path finding

**3. Distributed Systems**
- Content-addressable storage
- Merkle proofs (untrusted data sources)
- Deduplication

**4. Real-World Systems**
- Git internals
- Blockchain mechanics
- IPFS architecture

## Research Lineage

```
Merkle (1979)
"A Certified Digital Signature"
    ↓
Merkle (1980)
"Protocols for Public Key Cryptosystems"
    ↓
Bayer, Haber, Stornetta (1993)
"Improving the Efficiency and Reliability of Digital Time-Stamping"
    ↓
Git (2005)
Content-addressable file system
    ↓
Bitcoin (2009)
Merkle trees in blockchain
    ↓
IPFS (2014)
Merkle DAG for distributed storage
    ↓
Ethereum (2015)
Merkle Patricia Trie for state
    ↓
Certificate Transparency (2013-present)
Merkle logs for PKI transparency
```

**45+ years** of Merkle tree applications across diverse domains.

## Files

```
merkle-tree/
├── README.md          (this file)
├── merkle.scm         (implementation)
└── objects/           (content-addressable store, created on first use)
```

## Dependencies

- Chicken Scheme 5.x
- OpenSSL (for SHA-256: `openssl dgst`)

## Future Enhancements

**Performance:**
- [ ] Native SHA-256 (avoid subprocess overhead)
- [ ] Parallel tree construction
- [ ] Incremental updates (don't rebuild entire tree)

**Features:**
- [ ] Merkle Patricia Trie (key-value storage)
- [ ] Sparse Merkle Trees (large address spaces)
- [ ] Consistency proofs (prove append-only property)
- [ ] Multi-tree proofs (prove across multiple trees)

**Storage:**
- [ ] Persistent database backend (SQLite)
- [ ] Garbage collection (remove unreferenced objects)
- [ ] Compression (delta encoding for similar objects)

## License

Public domain. Based on Merkle's 1979 foundational research.

---

**"A single hash to authenticate them all."**
—The essence of Merkle's contribution to cryptography

**From paper to practice:**
Research (1979) → Git (2005) → Bitcoin (2009) → IPFS (2014) → Your projects (now)
