(memo
  (number 59)
  (title "Quantum Day Migration Plan")
  (date "January 2026 (2026-01-24T00:00:00Z)")
  (section
    "Abstract"
    (p "The TCB now has post-quantum signatures. ML-DSA-65 and SLH-DSA-SHAKE-256s are implemented, tested, and deployed. This Memo specifies the operational migration plan: how to transition existing Ed25519 keys, certificates, and vaults to quantum-resistant cryptography before Q-Day renders them forgeable."))
  (section
    "Status: Implementation Complete"
    (p "As of 2026-01-24, the SPKI TCB includes:")
    (list
      (item "ML-DSA-65 (FIPS 204): Lattice-based signatures, 3.3KB signatures")
      (item "SLH-DSA-SHAKE-256s (FIPS 205): Hash-based signatures, 29KB signatures")
      (item "Hybrid signature support: Ed25519 + PQ for transition period")
      (item "liboqs integration: Built WITHOUT OpenSSL dependency")
      (item "Comprehensive test suite: All tests passing"))
    (p "The theory is in Memo-048. This memo is about execution."))
  (section
    "The Migration Problem"
    (p "Every existing Cyberspace installation has:")
    (list
      (item "Ed25519 realm keys in ~/.cyberspace/vault/keystore")
      (item "Ed25519-signed capability certificates")
      (item "Ed25519-signed audit trail entries")
      (item "Ed25519-signed sealed releases"))
    (p "After Q-Day, all of these become forgeable. Migration is not optional."))
  (section
    "Migration Phases"
    (subsection
      "Phase 1: Hybrid Keys (Now - Q-Day minus 3 years)"
      (p "Generate hybrid keys that sign with BOTH Ed25519 and post-quantum algorithms:")
      (code scheme ";; In keystore initialization
(define (generate-hybrid-keypair)
  (let ((ed25519-pair (ed25519-keypair))
        (mldsa-pair (mldsa-keypair)))
    (keystore-add-key! 'ed25519 ed25519-pair)
    (keystore-add-key! 'ml-dsa-65 mldsa-pair)
    (keystore-set-mode! 'hybrid-sign)))")
      (p "Hybrid signatures verify if EITHER signature is valid during transition, but BOTH signatures are created. This allows:")
      (list
        (item "Legacy verifiers (Ed25519-only) still work")
        (item "Future verifiers (PQ-capable) get quantum resistance")
        (item "No flag day: gradual deployment"))
      (p "Action items:")
      (list
        (item "Run: cyberspace-vault upgrade-to-hybrid")
        (item "Verify: cyberspace-vault list-keys shows both key types")
        (item "Test: Sign and verify a test capability"))
      (p "Existing Ed25519 keys remain functional. New signatures include both algorithms."))
    (subsection
      "Phase 2: PQ Certificate Chains (Q-Day minus 2 years)"
      (p "Start issuing PQ-only certificates for NEW delegations:")
      (code scheme ";; When delegating capability
(cert-create
  (issuer-key (keystore-get-key 'ml-dsa-65))  ; Use PQ key
  (subject-key subject-mldsa-pubkey)
  (tag capability-tag)
  (signature-algorithm 'ml-dsa-65))")
      (p "Legacy certificates remain valid. Capability chains can mix:")
      (code "[Ed25519 cert] -> [Hybrid cert] -> [ML-DSA cert]")
      (p "Each link verified independently. The chain gains quantum resistance as PQ links are added."))
    (subsection
      "Phase 3: Mandatory PQ (Q-Day minus 1 year)"
      (p "Require at least ONE post-quantum signature in every capability chain:")
      (code scheme ";; Verification policy update
(define (verify-cert-chain chain)
  (let ((has-pq? (any (lambda (cert)
                        (memq (cert-algorithm cert)
                              '(ml-dsa-65 slh-dsa-shake-256s hybrid)))
                      chain)))
    (unless has-pq?
      (error \"Capability chain requires post-quantum signature\"))))")
      (p "This forces migration of critical paths while maintaining backwards compatibility for leaf nodes.")
      (p "Action items:")
      (list
        (item "Audit all capability chains: cyberspace-audit check-pq-coverage")
        (item "Re-sign pure-Ed25519 chains with hybrid mode")
        (item "Update delegation policies to prefer PQ recipients")))
    (subsection
      "Phase 4: Ed25519 Sunset (Q-Day)"
      (p "When quantum computers threaten Ed25519 (estimated 2030-2035):")
      (list
        (item "Ed25519 verification disabled for NEW operations")
        (item "Hybrid signatures verify ONLY the PQ component")
        (item "Pure Ed25519 certificates rejected")
        (item "Historical audit trail remains (for forensics, not trust)"))
      (code scheme ";; Q-Day configuration
(keystore-set-verification-policy!
  '(ml-dsa-65 slh-dsa-shake-256s)  ; Only PQ algorithms trusted
  '(ed25519))                      ; Ed25519 rejected")
      (p "Realms that failed to migrate become read-only. Their capabilities cannot be verified for new operations, but historical records persist."))
    (subsection
      "Phase 5: Pure PQ (Q-Day + 1 year)"
      (p "Complete transition to post-quantum-only:")
      (list
        (item "Remove Ed25519 from keystore except archival keys")
        (item "All new certificates use ML-DSA-65 or SLH-DSA")
        (item "Hybrid mode deprecated")
        (item "Ed25519 support removed from TCB in next major version"))
      (p "Cyberspace survives. The capability chain is quantum-resistant.")))
  (section
    "Algorithm Selection Guide"
    (subsection
      "ML-DSA-65 (Default Choice)"
      (p "Use for:")
      (list
        (item "Capability certificates (frequent issuance)")
        (item "Agent delegation (short-lived)")
        (item "Audit entries (high volume)")
        (item "Any certificate with < 10 year lifetime"))
      (p "Properties:")
      (table
        (header "Metric" "Value")
        (row "Public key" "1,952 bytes")
        (row "Signature" "3,309 bytes")
        (row "Security" "NIST Level 3 (128-bit PQ)")
        (row "Speed" "Fast signing & verification")
        (row "Basis" "Lattice problems (Module-LWE)")))
    (subsection
      "SLH-DSA-SHAKE-256s (Conservative Choice)"
      (p "Use for:")
      (list
        (item "Realm identity keys (root of trust)")
        (item "Sealed releases (archival)")
        (item "Long-term commitments (> 10 years)")
        (item "Maximum security requirement"))
      (p "Properties:")
      (table
        (header "Metric" "Value")
        (row "Public key" "64 bytes")
        (row "Signature" "29,792 bytes")
        (row "Security" "NIST Level 5 (128-bit PQ)")
        (row "Speed" "Slow signing, fast verification")
        (row "Basis" "SHAKE-256 hash only (conservative)")))
    (p "When in doubt, use ML-DSA-65. Only use SLH-DSA when you need maximum conservatism or archival guarantees."))
  (section
    "Operational Procedures"
    (subsection
      "Generate New Hybrid Keystore"
      (code bash "# Backup existing keystore
cp -r ~/.cyberspace/vault ~/.cyberspace/vault.ed25519.backup

# Generate hybrid keys (Ed25519 + ML-DSA-65)
cyberspace-vault init-hybrid

# Verify keys present
cyberspace-vault list-keys
# Expected output:
#   realm-ed25519: ed25519:7f3a2b4c...
#   realm-ml-dsa-65: ml-dsa-65:8a9b0c1d...
#   mode: hybrid-sign"))
    (subsection
      "Migrate Existing Vault"
      (code bash "# Add PQ key to existing vault
cyberspace-vault add-pq-key --algorithm ml-dsa-65

# Enable hybrid signing
cyberspace-vault set-mode hybrid

# Test hybrid signature
echo 'test message' | cyberspace-vault sign --hybrid
# Should produce signature with both Ed25519 and ML-DSA components"))
    (subsection
      "Re-sign Critical Certificates"
      (code bash "# List pure-Ed25519 certificates
cyberspace-cert list --algorithm ed25519 --critical-path

# Re-sign with hybrid
for cert in $(cyberspace-cert list --algorithm ed25519 --format ids); do
  cyberspace-cert resign --id $cert --algorithm hybrid
done

# Verify PQ coverage
cyberspace-audit check-pq-coverage"))
    (subsection
      "Verify PQ Implementation"
      (code bash "# Run TCB test suite
cd ~/cyberspace/spki/tcb
dune runtest

# Expected output:
#   test_tcb.exe: ✓ ALL TESTS PASSED
#   test_signature.exe: ✓ ALL TESTS PASSED
#   test_pq.exe: ✓ ALL TESTS PASSED
#     - ML-DSA-65: keygen, sign, verify: OK
#     - SLH-DSA: keygen, sign, verify: OK
#     - Invalid signature rejection: OK"))
    (subsection
      "Monitor Migration Progress"
      (code bash "# Capability chain coverage report
cyberspace-audit pq-coverage-report

# Example output:
#   Total capability chains: 1,247
#   Pure Ed25519: 89 (7.1%) ⚠️
#   Hybrid: 342 (27.4%)
#   Pure PQ: 816 (65.5%) ✓
#
#   Action required: 89 chains need PQ signatures")))
  (section
    "Rollback Strategy"
    (p "If post-quantum implementation has issues:")
    (subsection
      "Immediate Rollback"
      (code bash "# Disable PQ signing (keep Ed25519 only)
cyberspace-vault set-mode ed25519-only

# This maintains compatibility but loses quantum resistance
# Use only in emergency"))
    (subsection
      "Partial Rollback"
      (code bash "# Keep hybrid mode but prefer Ed25519
cyberspace-vault set-mode hybrid --prefer ed25519

# Both signatures still created, but Ed25519 is primary for verification
# Provides fallback while keeping PQ signatures for future"))
    (p "Rollback preserves existing PQ signatures. You can re-enable PQ verification later without re-signing."))
  (section
    "Testing Strategy"
    (subsection
      "Unit Tests"
      (p "TCB test suite (test_pq.ml) validates:")
      (list
        (item "ML-DSA-65 keypair generation from system randomness")
        (item "SLH-DSA keypair generation")
        (item "Signature creation and verification")
        (item "Invalid signature rejection")
        (item "Backward compatibility with Ed25519"))
      (code bash "# Run continuously during development
cd ~/cyberspace/spki/tcb && dune runtest"))
    (subsection
      "Integration Tests"
      (p "Test capability delegation across algorithm boundaries:")
      (code scheme ";; Create mixed chain: Ed25519 -> Hybrid -> ML-DSA
(define chain
  (list
    (cert-create issuer-ed25519 subject-hybrid (read-tag))
    (cert-create issuer-hybrid subject-mldsa (read-tag))))

;; Verify chain validates
(verify-cert-chain chain)"))
    (subsection
      "Interoperability Tests"
      (p "Test against other SPKI implementations:")
      (list
        (item "Can legacy Ed25519-only verifiers handle hybrid certs? (YES - they verify Ed25519 component)")
        (item "Can PQ-only verifiers handle hybrid certs? (YES - they verify PQ component)")
        (item "Do certificate chains mix algorithms correctly? (YES - each link verified independently)")))
    (subsection
      "Performance Tests"
      (p "Measure signing/verification latency:")
      (code scheme ";; Benchmark signing operations
(time
  (let loop ((i 0))
    (when (< i 1000)
      (mldsa-sign test-message test-key)
      (loop (+ i 1)))))

;; Expected: ~0.5ms per ML-DSA signature on modern hardware
;; SLH-DSA: ~50ms per signature (acceptable for infrequent operations)"))
    (subsection
      "Stress Tests"
      (p "Verify scaling with large certificate chains:")
      (code bash "# Generate chain with 100 links, all PQ signatures
cyberspace-test generate-chain --length 100 --algorithm ml-dsa-65

# Verify chain validates in reasonable time
# Expected: < 100ms for 100-link ML-DSA chain")))
  (section
    "Security Considerations"
    (subsection
      "Harvest-Now-Forge-Later Defense"
      (p "Hybrid signatures defend against harvest attacks:")
      (list
        (item "Attacker records Ed25519 signature today")
        (item "Attacker breaks Ed25519 with quantum computer on Q-Day")
        (item "Attacker CANNOT forge because ML-DSA signature still secure")
        (item "Defense works even if Ed25519 is broken retroactively"))
      (p "This is why hybrid mode is critical during transition: it provides quantum resistance even for signatures created before migration."))
    (subsection
      "Algorithm Agility Risks"
      (p "Supporting multiple algorithms increases attack surface:")
      (list
        (item "More code paths = more bugs")
        (item "Downgrade attacks if implementation allows algorithm negotiation")
        (item "Version confusion if different nodes support different algorithms"))
      (p "Mitigations:")
      (list
        (item "No algorithm negotiation: verifiers accept listed algorithms, signers choose based on policy")
        (item "Explicit algorithm in certificate: (signature-algorithm 'ml-dsa-65)")
        (item "Conservative verification: if ANY supported algorithm validates, accept")))
    (subsection
      "Key Management"
      (p "PQ keys are larger than Ed25519:")
      (table
        (header "Key Type" "Private Key Size" "Backup Impact")
        (row "Ed25519" "64 bytes" "trivial")
        (row "ML-DSA-65" "4,032 bytes" "63x larger")
        (row "SLH-DSA" "128 bytes" "2x larger"))
      (p "Implications:")
      (list
        (item "Paper backups harder (4KB vs 64B seed)")
        (item "Hardware security modules may need firmware updates")
        (item "Key splitting schemes need larger shares"))
      (p "Solution: Derive ML-DSA keys from 32-byte seed, store seed instead of full key. This maintains small backup size."))
    (subsection
      "Timing Side Channels"
      (p "Post-quantum algorithms are timing-sensitive:")
      (list
        (item "Lattice operations (ML-DSA) use rejection sampling")
        (item "Hash operations (SLH-DSA) are constant-time by construction")
        (item "liboqs claims constant-time implementations"))
      (p "Testing: Profile signing operations for variance. Large variance suggests timing leaks. ML-DSA rejection sampling should be bounded, not unbounded."))
    (subsection
      "Dependency Trust"
      (p "TCB now depends on two crypto libraries:")
      (table
        (header "Library" "LOC (approx)" "Audit Status" "Concerns")
        (row "libsodium" "50K" "Well-audited" "Trusted")
        (row "liboqs" "200K" "Research-quality" "Newer, evolving"))
      (p "Risk mitigation:")
      (list
        (item "liboqs built WITHOUT OpenSSL (no transitive dependency)")
        (item "Only use NIST-standardized algorithms (ML-DSA, SLH-DSA)")
        (item "Pin liboqs version, audit before upgrades")
        (item "Hybrid signatures provide defense-in-depth: even if liboqs has bug, Ed25519 component still validates during transition"))))
  (section
    "Timeline Recommendations"
    (subsection
      "Immediate (2026)"
      (list
        (item "Enable hybrid signing for all new vaults")
        (item "Add PQ keys to existing high-value vaults")
        (item "Begin re-signing critical capability chains")))
    (subsection
      "Near-term (2027)"
      (list
        (item "Require hybrid or pure-PQ for root realm keys")
        (item "Mandate at least one PQ signature per capability chain")
        (item "Deprecate pure-Ed25519 for new certificates")))
    (subsection
      "Medium-term (2028-2030)"
      (list
        (item "Pure-PQ becomes default for new vaults")
        (item "Ed25519 verification only for historical audit")
        (item "Monitor NIST PQC standardization updates")))
    (subsection
      "Q-Day Response"
      (list
        (item "If quantum threat emerges: immediately disable Ed25519 verification")
        (item "Hybrid signatures fall back to PQ component only")
        (item "Unmigrated vaults freeze (read-only)")
        (item "Post-migration vaults continue operating"))
      (p "The migration MUST complete before Q-Day. Reacting after the break is too late: attackers already harvested your signatures.")))
  (section
    "Verification Checklist"
    (p "Before declaring migration complete:")
    (code "☐ TCB tests passing (dune runtest)
☐ Vault has hybrid or pure-PQ keys
☐ All critical capability chains have ≥1 PQ signature
☐ Signing operations succeed with PQ algorithms
☐ Verification accepts PQ signatures
☐ Backup includes PQ keys (encrypted)
☐ Audit trail shows PQ signature usage
☐ Interoperability tested with legacy verifiers
☐ Performance acceptable (< 1ms for ML-DSA signing)
☐ Rollback procedure tested and documented"))
  (section
    "References"
    (list
      (item "Memo-048: Post-Quantum Signatures (theory and design)")
      (item "FIPS 204: Module-Lattice-Based Digital Signature Standard")
      (item "FIPS 205: Stateless Hash-Based Digital Signature Standard")
      (item "PQ-IMPLEMENTATION.md: TCB implementation details")
      (item "liboqs documentation: https://github.com/open-quantum-safe/liboqs")))
  (section
    "Conclusion"
    (p "Post-quantum cryptography is not a future problem. It's a migration problem happening now. Every Ed25519 signature created today is a potential forgery after Q-Day.")
    (p "The implementation is complete. The tools exist. The question is not 'can we migrate' but 'will we migrate in time.'")
    (p "Harvest-now-forge-later is not theoretical. Adversaries are already recording traffic. The clock is ticking.")
    (p "Migrate before Q-Day. Not after.")))
