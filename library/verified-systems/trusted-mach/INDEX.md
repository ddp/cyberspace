# Trusted Mach and DTOS: Secure Microkernel Research

This collection contains papers on Trusted Mach and the Distributed Trusted Operating System (DTOS) project, which pioneered flexible security architectures for microkernel-based systems.

## What is Trusted Mach?

**Mach** was a microkernel operating system developed at Carnegie Mellon University (CMU) in the 1980s. It influenced:
- macOS and iOS (Darwin kernel is based on Mach)
- NeXTSTEP (Steve Jobs' OS)
- GNU Hurd
- Many research operating systems

**Trusted Mach** extended Mach with:
- Mandatory Access Control (MAC)
- Type Enforcement (TE)
- Flexible security policies
- Minimal Trusted Computing Base (TCB)

## The DTOS Project

**DTOS = Distributed Trusted Operating System**
- Funded by DARPA and NSA
- Goal: Secure distributed computing
- Based on Mach 3.0 microkernel
- Developed by Secure Computing Corporation and University of Utah

**Key Innovation:**
> "Policy-neutral" access control - security policy implemented outside the kernel

## The Papers

### dtos-policy-neutral-access-control.pdf
**Developing and Using a "Policy Neutral" Access Control Policy**
- Spencer, Smalley, Loscocco, Hibler, Andersen, Lepreau
- NSPW 1996 (New Security Paradigms Workshop)
- **THE POLICY FLEXIBILITY PAPER**

**The Problem with Traditional Security:**
- Security policy **hardcoded** into kernel
- Examples:
  - Unix: DAC (Discretionary Access Control) only
  - Trusted Solaris: Bell-LaPadula MLS (Multi-Level Security)
- Cannot change policy without rewriting kernel

**DTOS Solution: Flask Architecture**
- **Separate mechanism from policy**
- Kernel enforces decisions, policy server makes decisions
- Policy defined in user space
- Can switch policies without kernel changes

**Architecture:**
```
Application
    ↓
Object Manager (in kernel)
    ↓
Security Server (user space)
    ↓
Policy Database (loadable)
```

**Policy Examples:**
1. **Bell-LaPadula MLS**: No read up, no write down (military classification)
2. **Biba Integrity**: No read down, no write up (commercial integrity)
3. **Chinese Wall**: Conflict of interest prevention (consulting firms)
4. **Type Enforcement**: Domain separation (app sandboxing)
5. **Custom policies**: Organization-specific rules

**The "Policy Neutral" Concept:**
- Kernel provides **mechanisms** (object labeling, access checks)
- User space provides **policy** (what's allowed)
- Same kernel supports radically different policies

**Impact:**
- Influenced SELinux (Security-Enhanced Linux)
- Flask architecture became NSA standard
- Led to modern LSM (Linux Security Modules)

### dtos-mach-kernel-interfaces.pdf
**DTOS Mach Kernel Interfaces**
- Secure Computing Corporation
- Technical specification document
- **THE IMPLEMENTATION DETAILS**

**Kernel Security Controls:**
1. **Port Security**: IPC endpoint access control
2. **Task Security**: Process isolation and capabilities
3. **Thread Security**: Execution context protection
4. **Virtual Memory Security**: Page-level access control
5. **Device Security**: Hardware access mediation

**Security Labels:**
- Every object has security attributes
- Stored in kernel's security context
- Checked on every operation

**Trusted Path:**
- Guarantees user communicates with real login
- Prevents Trojan login screens
- Critical for high-assurance systems

**Audit Trail:**
- Records all security-relevant events
- Tamper-evident logging
- Required for Common Criteria evaluation

**Least Privilege:**
- Processes start with minimal capabilities
- Must explicitly request privileges
- Kernel grants based on policy

### security-enhanced-darwin-selinux.pdf
**Security-Enhanced Darwin: Porting SELinux to Mac OS X**
- Christopher Vance and others
- **MODERN DESCENDANT OF TRUSTED MACH**

**The Connection:**
- macOS Darwin kernel = Mach + BSD
- SELinux = Flask architecture (from DTOS/Trusted Mach)
- Project: Add SELinux security to macOS

**Why This Matters:**
- Shows Trusted Mach concepts portable to modern systems
- Demonstrates policy flexibility works on commodity OS
- Bridges research and practice

**Flask Security Architecture in Darwin:**
- Object managers (file system, IPC, network)
- Security server (policy decisions)
- Access Vector Cache (performance optimization)

**Challenges:**
- macOS has different object model than Linux
- Frameworks (Cocoa) not security-aware
- Application compatibility concerns

**Results:**
- Proof-of-concept successful
- Demonstrates feasibility
- Performance overhead acceptable (~5%)

**Current Status:**
- Not officially adopted by Apple
- Apple has own MAC framework (TrustedBSD MAC)
- Influenced macOS security features (sandboxing, entitlements)

### mach-microkernel-architecture.pdf
**Microkernel Operating System Architecture and Mach**
- Classic Mach architecture paper
- **THE MACH FOUNDATION**

**Mach's Core Abstractions:**
1. **Task**: Address space + resources (≈ process)
2. **Thread**: Execution unit within task
3. **Port**: IPC communication endpoint
4. **Message**: Data sent between ports
5. **Memory Object**: Abstract memory backing store

**IPC (Inter-Process Communication):**
- Port-based messaging
- Location-transparent (local or remote)
- Capability-based security (port rights)

**External Pagers:**
- Page fault handling in user space
- Multiple paging policies possible
- Flexibility for distributed systems

**Problems with Original Mach:**
- IPC was slow (~100 µs)
- Kernel too large
- Led to Liedtke's L4 research (see ../l4-microkernel/)

**Mach's Legacy:**
- **macOS/iOS**: Darwin kernel = Mach 3.0 + BSD
- **NeXTSTEP**: Original Mach-based OS
- **GNU Hurd**: Still in development
- **Trusted systems**: DTOS, Flask, SELinux lineage

## The Security Architecture Evolution

**Timeline:**
1. **1985**: Mach microkernel (CMU)
2. **1990s**: DTOS project (Flask architecture)
3. **1996**: "Policy Neutral" access control paper
4. **2000**: SELinux released by NSA (based on Flask)
5. **2001**: SELinux merged into Linux kernel
6. **2003**: SELinux in Fedora/Red Hat
7. **2000s**: TrustedBSD MAC Framework (FreeBSD, macOS)
8. **2010s**: Android SELinux (mandatory on Android 5.0+)

## Flask Architecture Descendants

**SELinux (Security-Enhanced Linux):**
- NSA implementation of Flask for Linux
- Type Enforcement + Role-Based Access Control
- Mandatory on Android, Red Hat Enterprise Linux
- Same policy-neutral approach as DTOS

**AppArmor:**
- Alternative to SELinux (path-based)
- Used in Ubuntu, SUSE
- Less flexible but easier to configure

**TrustedBSD MAC Framework:**
- FreeBSD security framework
- Multiple loadable policies
- Used in macOS (Darwin)

**Capsicum:**
- Capability-based security (FreeBSD, Linux)
- Process sandboxing
- Used in Chrome, FreeBSD

## Why Policy-Neutral Security Matters

**Traditional Approach:**
```
Application
    ↓
OS with hardcoded security policy
    ↓
Hardware
```
- Policy change requires kernel modification
- One-size-fits-all security
- Inflexible

**DTOS/Flask Approach:**
```
Application
    ↓
Kernel (mechanism only)
    ↓
Security Server (policy)
    ↓
Loadable policy database
```
- Policy change is configuration, not code
- Multiple policies supported
- Adaptable to different environments

**Real-World Examples:**

**Military (Bell-LaPadula):**
- TOP SECRET > SECRET > CONFIDENTIAL > UNCLASSIFIED
- No read up, no write down
- Prevent information leakage

**Commercial (Biba):**
- Prevent low-integrity data from corrupting high-integrity
- Financial systems, medical records
- Data integrity over confidentiality

**Android (SELinux):**
- App sandboxing
- System service isolation
- Prevent privilege escalation

## DTOS Performance

**Security Overhead:**
- Label checks: ~5% performance cost
- Most overhead in policy decision caching
- Acceptable for high-assurance systems

**Optimization Techniques:**
- Access Vector Cache (AVC): Cache policy decisions
- Security ID (SID) compaction: Small label identifiers
- Fast path for common operations

## Comparison with Other Secure Systems

| System | Kernel | Policy Mechanism | Flexibility | Verification |
|--------|--------|-----------------|-------------|--------------|
| **Trusted Mach/DTOS** | Mach 3.0 | Flask (Type Enforcement) | High | Testing |
| SELinux | Linux | Flask (TE + RBAC) | High | Testing |
| seL4 | L4 | Capabilities | Medium | Formal proof |
| Trusted Solaris | SVR4 | Bell-LaPadula MLS | Low | Testing |
| Windows (Mandatory Integrity) | NT | Integrity levels | Low | Testing |

## The Type Enforcement Model

**Core Idea:**
- Subjects (processes) have **domains**
- Objects (files, ports) have **types**
- Policy specifies: domain D can access type T with permissions P

**Example:**
```
Domain: web_server_t
Type: web_content_t
Rule: allow web_server_t web_content_t:file { read getattr };

Domain: web_server_t
Type: database_t
Rule: DENY (no rule = implicit deny)
```

**Benefits:**
- Fine-grained control
- Least privilege enforcement
- Clear separation of concerns
- Prevents many classes of attacks

## DTOS and the High-Assurance Community

**Common Criteria Evaluation:**
- DTOS targeted EAL6 (high robustness)
- Policy-neutral approach aided evaluation
- Flexible policies for different threat models

**Defense Applications:**
- Classified data processing
- Cross-domain solutions
- High-assurance guards
- Separation kernels

**Research Impact:**
- Proved policy flexibility viable
- Influenced MILS (Multiple Independent Levels of Security)
- Led to modern separation kernels

## Limitations and Lessons Learned

**What Worked:**
- ✓ Policy-neutral architecture is practical
- ✓ Type Enforcement is powerful and flexible
- ✓ Performance overhead acceptable
- ✓ Security properties provable (with effort)

**What Didn't:**
- ✗ Policy complexity: Hard to write correct policies
- ✗ Application compatibility: Legacy apps not aware of MAC
- ✗ User confusion: "Why can't I access my own file?"
- ✗ Deployment: Complex to configure

**Modern Solutions:**
- Better default policies (SELinux targeted policy)
- Tools for policy analysis (sepolicy, audit2allow)
- Gradual rollout (SELinux permissive mode)
- Container-era renaissance (Kubernetes + SELinux)

## Connection to Modern Security

**Docker/Kubernetes:**
- SELinux integration for container isolation
- Type Enforcement prevents container breakout
- Policy-neutral approach allows custom rules

**Android Security:**
- Every app is a SELinux domain
- System services are isolated types
- OTA updates can change policy

**IoT Security:**
- Embedded Linux + SELinux
- Minimal TCB like DTOS
- Verified boot chains

## The Mach Legacy in Modern Systems

**macOS/iOS (Darwin):**
- Mach 3.0 microkernel core
- BSD Unix personality
- XNU (X is Not Unix) hybrid kernel
- TrustedBSD MAC Framework (Flask-inspired)

**GNU Hurd:**
- Still in development (since 1990!)
- Pure microkernel design
- Multiple server processes
- Research platform

## Sources

Papers obtained from:
- University of Utah Flux research group: https://www.cs.utah.edu/flux/
- NSPW (New Security Paradigms Workshop) proceedings
- Secure Computing Corporation technical reports
- UC Berkeley and CMU course materials

## Further Reading

For verified secure microkernels:
- ../sel4/ - Formally verified L4-based kernel
- ../l4-microkernel/ - Minimal high-performance microkernels

For security policy languages:
- SELinux documentation (modern Flask implementation)
- AppArmor documentation (alternative approach)

For formal verification of security properties:
- ../coq/ - Theorem proving for verified systems
