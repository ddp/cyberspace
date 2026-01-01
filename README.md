# cyberspace

Personal knowledge repository for distributed systems, cryptographic security, protocol design, and computer science research.

**Theme**: Distributed computational identity with cryptographic verification

**Updated**: 2025-12-31

## Repository Structure

### Research Collections

**[lamport-papers/](lamport-papers/INDEX.md)** - Leslie Lamport Papers
- 15 seminal papers on distributed systems and consensus
- Paxos, Byzantine fault tolerance, logical clocks, temporal logic
- 2013 ACM Turing Award winner
- See [INDEX.md](lamport-papers/INDEX.md) for full catalog

**[dec-vaxcluster-papers/](dec-vaxcluster-papers/INDEX.md)** - DEC VAXcluster & SCS Architecture
- 9 papers on VAXcluster distributed systems
- Systems Communication Architecture (SCA/SCS)
- DEC research reports (SRC, WRL)
- See [INDEX.md](dec-vaxcluster-papers/INDEX.md) for full catalog

**[dssa-ncsc-papers/](dssa-ncsc-papers/INDEX.md)** - Digital DSSA & NCSC Proceedings
- Digital's Distributed System Security Architecture (1989)
- NCSC conference proceedings (1987-1992)
- DASS and IPsec RFCs (Kaufman, Piper)
- 133 MB of foundational security research
- See [INDEX.md](dssa-ncsc-papers/INDEX.md) for full catalog

**[network-alchemy-patents/](network-alchemy-patents/INDEX.md)** - Network Alchemy IP Clustering
- TCP/IP clustering and load balancing patents
- Hash-based session distribution
- Certificate enrollment protocols
- Acquired by Nokia (2000)
- See [INDEX.md](network-alchemy-patents/INDEX.md) for full catalog

**[library/](library/)** - Technical Library (671 MB)
- 312 PDFs: papers, books, technical documentation
- Topics: cryptography, security, OS design, programming languages
- Distributed systems, networking, compilers, formal methods
- Organized in subdirectories by topic

**[chicken-scheme-eggs/](chicken-scheme-eggs/)** - Chicken Scheme Documentation
- 18 egg documentation files extracted from wiki.call-cc.org
- tcp6, udp6, json, loops, formatting, URI handling
- Reference documentation for Scheme development

### Design Documents

**[distributed-agent-architecture.md](distributed-agent-architecture.md)**
- Cryptographically-secured agent cluster architecture
- Shamir threshold cryptography, CRDTs, Byzantine tolerance
- Event sourcing, actor model semantics
- Application of Lamport/DSSA concepts to modern agents

**[common-lisp-hyperspec.md](common-lisp-hyperspec.md)**
- Quick reference guide to ANSI Common Lisp HyperSpec
- Chapter-by-chapter navigation
- Symbol indexes and glossary links

### Configuration Files

**[.emacs](.emacs)** - Emacs configuration (~700 lines)
- SLY (Common Lisp), tuareg (OCaml), paredit (Scheme), lua-mode
- Custom keymap (`C-c d`), TRAMP multi-hop SSH
- Package management via MELPA/GNU ELPA

**[.zshrc](.zshrc)** - Zsh shell configuration (~250 lines)
- Homebrew detection (Apple Silicon + Intel)
- SSH completion, emacsclient wrappers
- opam/SBCL integration, REPL aliases

**[CLAUDE.md](CLAUDE.md)** - Project instructions for Claude Code
- Repository overview and file structure
- Key configurations and custom functions
- Testing and deployment procedures

### Indexes

**[PERMUTED-INDEX.md](PERMUTED-INDEX.md)** - Fully Permuted KeyWord In Context Index
- 53 unique documents indexed by every significant term
- LaTeX makeindex style (inspired by Common Lisp HyperSpec)
- Cross-references across all research collections

## Key Themes

### Distributed Systems
- Consensus algorithms (Paxos, Byzantine Generals)
- Causality and logical clocks
- Distributed snapshots and global states
- Cluster architectures (VAXcluster, IP clustering)

### Cryptographic Security
- Digital DSSA (no central authority)
- Public key infrastructure and certificates
- IPsec/ISAKMP key exchange
- Threshold cryptography (Shamir secret sharing)

### Protocol Design
- TCP state management and failover
- Load balancing and session affinity
- Certificate enrollment protocols
- Secure distributed coordination

### Formal Methods
- TLA+ specification language
- Safety and liveness properties
- Temporal logic and model checking
- Sequential consistency

## Historical Lineage

This repository traces the evolution of distributed security from foundational research to commercial implementation:

**1970s-1980s**: Lamport establishes distributed systems theory
→ Logical clocks, Byzantine fault tolerance, Paxos consensus

**1989**: Digital DSSA defines distributed security architecture
→ No central authority, certificate-based authentication

**1990s**: Practical implementations emerge
→ VAXcluster SCS, Network Alchemy IP clustering, IPsec/IKE

**2020s**: Modern distributed agents
→ Cryptographic identity, eventual consistency, actor models

## Related Work

### Academic Foundations
- Leslie Lamport (causality, consensus, Byzantine tolerance)
- Butler Lampson (capability-based security, DSSA)
- Shamir (secret sharing), Fidge/Mattern (vector clocks)

### Commercial Systems
- DEC VAXcluster (distributed lock manager, SCS/SCA)
- Network Alchemy (TCP/IP clustering, certificate enrollment)

### Modern Applications
- Distributed databases (Spanner, CockroachDB using Paxos)
- Blockchain consensus (Byzantine tolerance)
- Service meshes (load balancing, health checks)
- Zero-trust security (certificate-based identity)

## Usage

### For Research
- Start with [PERMUTED-INDEX.md](PERMUTED-INDEX.md) to find topics
- Read collection INDEX.md files for context
- PDFs in [library/](library/) for deep reading

### For Protocol Design
- [dssa-ncsc-papers/](dssa-ncsc-papers/INDEX.md) - Authentication and security
- [network-alchemy-patents/](network-alchemy-patents/INDEX.md) - Load balancing and failover
- [lamport-papers/](lamport-papers/INDEX.md) - Consensus and causality

### For Distributed Agent Development
- [distributed-agent-architecture.md](distributed-agent-architecture.md) - System design
- [lamport-papers/](lamport-papers/INDEX.md) - Paxos, Byzantine tolerance, logical clocks
- [dssa-ncsc-papers/](dssa-ncsc-papers/INDEX.md) - Certificate-based authentication
- [network-alchemy-patents/](network-alchemy-patents/INDEX.md) - Clustering patterns

## Statistics

- **Research Papers**: 53 indexed documents
- **Technical Library**: 312 PDFs (671 MB)
- **Documentation**: 27 markdown files
- **Collections**: 6 specialized subdirectories
- **Total Repository Size**: ~800 MB

## Deployment

These dotfiles are designed to be symlinked from the home directory:

```bash
cd ~
git clone <repo-url> cyberspace
ln -s ~/cyberspace/.emacs ~/.emacs
ln -s ~/cyberspace/.zshrc ~/.zshrc
```

## Contributing

This is a personal knowledge repository, but corrections and additions to documentation are welcome.

## License

- **Dotfiles** (.emacs, .zshrc): Personal configuration, use freely
- **Documentation** (*.md): Original work, CC BY 4.0
- **Papers/PDFs**: Respective copyright holders (research/educational use)

## Acknowledgments

- Leslie Lamport (papers and inspiration)
- Butler Lampson and Digital DSSA team
- DEC research labs (SRC, WRL)
- Network Alchemy team (Derrell Piper et al.)
- NIST/NSA NCSC conference organizers
- LispWorks Ltd. (Common Lisp HyperSpec)
- Chicken Scheme community

---

**Curator**: Personal research repository for distributed agent systems with cryptographic security
**Contact**: See IETF datatracker or repository commit history
**Last Updated**: 2025-12-31
