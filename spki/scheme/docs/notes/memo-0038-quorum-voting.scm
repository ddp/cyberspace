;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 38)
  (title "Quorum Protocol with Homomorphic Voting")
  (section
    "Abstract"
    (p "This Memo specifies the quorum protocol for the Library of Cyberspace: how principals reach collective decisions through homomorphic encryption-based voting, enabling private ballot tallying without revealing individual votes. Quorum integrates with threshold governance (Memo-008) and Byzantine consensus (Memo-011)."))
  (section
    "Motivation"
    (p "Collective decisions require:")
    (list
      (item "Privacy")
      (item "Voters shouldn't know how others voted")
      (item "Verifiability")
      (item "Results must be provably correct")
      (item "Coercion resistance")
      (item "Can't prove how you voted to others")
      (item "Availability")
      (item "Voting continues despite failures"))
    (p "Voting systems that sacrifice any of these properties enable manipulation; true collective decision requires all four.")
    (p "Traditional approaches fail:")
    (list
      (item "Open ballot")
      (item "No privacy, enables coercion")
      (item "Trusted tallier")
      (item "Single point of compromise")
      (item "Secure multi-party computation")
      (item "Complex, high communication overhead"))
    (p "Each failure mode represents a fundamental architectural limitation, not merely an implementation weakness.")
    (p "None of these approaches fits a decentralized, trustless environment.")
    (p "Homomorphic encryption provides:")
    (list
      (item "Vote on encrypted ballots")
      (item "Sum without decryption")
      (item "Decrypt only the final tally")
      (item "Mathematical proof of correctness"))
    (p "Homomorphic encryption resolves the apparent paradox: computing on data without seeing it.")))
  (section
    "Cryptographic Foundation"
    (subsection
      "Homomorphic Encryption Schemes"
      (table
        (header "Scheme " "Operations " "Performance " "Use Case ")
        (row "Paillier " "Addition " "Fast " "Vote tallying ")
        (row "BFV/BGV " "Add + Multiply " "Medium " "Complex predicates ")
        (row "TFHE " "Arbitrary " "Slow " "General computation "))
      (p "For quorum voting, Paillier suffices - we only need addition."))
    (subsection
      "Paillier Properties"
      (code scheme ";; Additive homomorphism\n(= (decrypt (he-add (encrypt a) (encrypt b)))\n   (+ a b))\n\n;; Scalar multiplication via repeated addition\n(= (decrypt (he-scalar-mult (encrypt a) k))\n   (* a k))\n\n;; Semantic security - ciphertexts indistinguishable\n(not (distinguishable? (encrypt 0) (encrypt 1)))"))
    (subsection
      "Key Generation"
      (code scheme "(define-record-type <quorum-keys>\n  (make-quorum-keys public private threshold shares)\n  quorum-keys?\n  (public qk-public)           ; Public encryption key\n  (private qk-private)         ; Private decryption key (or #f if distributed)\n  (threshold qk-threshold)     ; M-of-N threshold\n  (shares qk-shares))          ; Distributed key shares\n\n(define (generate-quorum-keys bit-length threshold trustees)\n  \"Generate threshold Paillier keys\"\n  (let* ((keys (paillier-keygen bit-length))\n         (shares (shamir-split (paillier-private keys)\n                               threshold\n                               (length trustees))))\n    (make-quorum-keys\n      (paillier-public keys)\n      #f  ; No single party holds private key\n      threshold\n      (map cons trustees shares))))")))
  (section
    "Ballot Structure"
    (subsection
      "Ballot Definition"
      (code scheme "(define-record-type <ballot>\n  (make-ballot id question options threshold deadline)\n  ballot?\n  (id ballot-id)                 ; Content hash\n  (question ballot-question)     ; Human-readable question\n  (options ballot-options)       ; List of choices\n  (threshold ballot-threshold)   ; Votes needed to pass\n  (deadline ballot-deadline))    ; Voting closes\n\n;; Example ballot\n(make-ballot\n  id: \"sha256:ballot...\"\n  question: \"Accept Memo-042 into standard?\"\n  options: '(accept reject abstain)\n  threshold: '(majority members)  ; >50% of members\n  deadline: 1767786000)"))
    (subsection
      "Encrypted Vote"
      (code scheme "(define-record-type <encrypted-vote>\n  (make-encrypted-vote ballot-id voter ciphertext proof timestamp signature)\n  encrypted-vote?\n  (ballot-id vote-ballot-id)     ; Which ballot\n  (voter vote-voter)             ; Voter's public key (or anonymous token)\n  (ciphertext vote-ciphertext)   ; HE-encrypted choice\n  (proof vote-proof)             ; Zero-knowledge proof of validity\n  (timestamp vote-timestamp)\n  (signature vote-signature))"))
    (subsection
      "Vote Encoding"
      (code scheme ";; One-hot encoding for multiple choices\n;; accept=1, reject=0, abstain=0 → (1, 0, 0)\n\n(define (encode-vote choice options)\n  \"Encode choice as one-hot vector\"\n  (map (lambda (opt)\n         (if (eq? opt choice) 1 0))\n       options))\n\n(define (encrypt-vote choice options public-key)\n  \"Encrypt one-hot encoded vote\"\n  (map (lambda (v)\n         (paillier-encrypt public-key v))\n       (encode-vote choice options)))\n\n;; Vote for \"accept\"\n(encrypt-vote 'accept '(accept reject abstain) pub-key)\n;; => (Enc(1), Enc(0), Enc(0))")))
  (section
    "Voting Protocol"
    (subsection
      "Phase 1: Ballot Creation"
      (code scheme "(define (create-ballot question options threshold deadline trustees)\n  \"Create new ballot with threshold decryption\"\n  (let* ((keys (generate-quorum-keys 2048\n                                     (ceiling (/ (length trustees) 2))\n                                     trustees))\n         (ballot (make-ballot\n                   question: question\n                   options: options\n                   threshold: threshold\n                   deadline: deadline)))\n    ;; Distribute key shares to trustees\n    (for-each (lambda (trustee share)\n                (secure-send trustee\n                  `(key-share\n                    (ballot-id ,(ballot-id ballot))\n                    (share ,share))))\n              trustees\n              (qk-shares keys))\n    ;; Publish ballot\n    (soup-put ballot type: 'ballot)\n    (audit-append action: 'ballot-created\n                  ballot: (ballot-id ballot))\n    ballot))"))
    (subsection
      "Phase 2: Vote Casting"
      (code scheme "(define (cast-vote ballot choice voter-key)\n  \"Cast encrypted vote with validity proof\"\n  (let* ((pub-key (ballot-public-key ballot))\n         (encrypted (encrypt-vote choice (ballot-options ballot) pub-key))\n         (proof (generate-validity-proof encrypted choice pub-key))\n         (vote (make-encrypted-vote\n                 ballot-id: (ballot-id ballot)\n                 voter: (key->principal voter-key)\n                 ciphertext: encrypted\n                 proof: proof\n                 timestamp: (current-time))))\n    ;; Sign the vote\n    (set-encrypted-vote-signature! vote\n      (sign-vote voter-key vote))\n    ;; Submit\n    (submit-vote vote)\n    vote))\n\n(define (submit-vote vote)\n  \"Submit vote to ballot coordinator\"\n  ;; Verify eligibility\n  (unless (eligible-voter? (vote-voter vote) (vote-ballot-id vote))\n    (error 'not-eligible))\n  ;; Verify validity proof\n  (unless (verify-validity-proof vote)\n    (error 'invalid-vote-proof))\n  ;; Verify not already voted\n  (when (already-voted? (vote-voter vote) (vote-ballot-id vote))\n    (error 'already-voted))\n  ;; Record vote\n  (soup-put vote type: 'encrypted-vote)\n  (audit-append action: 'vote-cast\n                ballot: (vote-ballot-id vote)\n                voter: (vote-voter vote)))"))
    (subsection
      "Phase 3: Homomorphic Tallying"
      (code scheme "(define (tally-votes ballot)\n  \"Homomorphically sum all votes\"\n  (let* ((votes (soup-query type: 'encrypted-vote\n                            ballot-id: (ballot-id ballot)))\n         (num-options (length (ballot-options ballot)))\n         (zero-tally (make-list num-options (paillier-encrypt-zero))))\n    ;; Sum encrypted votes\n    (fold (lambda (vote tally)\n            (map paillier-add\n                 (vote-ciphertext vote)\n                 tally))\n          zero-tally\n          votes)))\n\n;; After tallying 100 votes:\n;; (Enc(47), Enc(41), Enc(12))\n;; Still encrypted - no one knows the result yet"))
    (subsection
      "Phase 4: Threshold Decryption"
      (code scheme "(define (decrypt-tally ballot encrypted-tally)\n  \"Threshold decrypt the tally\"\n  (let* ((trustees (ballot-trustees ballot))\n         (threshold (ballot-key-threshold ballot))\n         (shares '()))\n    ;; Collect decryption shares\n    (for-each (lambda (trustee)\n                (let ((share (request-decryption-share trustee\n                               (ballot-id ballot)\n                               encrypted-tally)))\n                  (when share\n                    (set! shares (cons share shares)))))\n              trustees)\n    ;; Need threshold shares\n    (unless (>= (length shares) threshold)\n      (error 'insufficient-decryption-shares))\n    ;; Combine shares to decrypt\n    (let ((plaintext-tally\n           (map (lambda (ct)\n                  (threshold-decrypt ct shares))\n                encrypted-tally)))\n      ;; Publish result\n      (publish-result ballot plaintext-tally)\n      plaintext-tally)))\n\n(define (request-decryption-share trustee ballot-id encrypted-tally)\n  \"Request trustee's decryption share\"\n  (let ((response (tunnel trustee\n                    `(decryption-share-request\n                      (ballot-id ,ballot-id)\n                      (tally ,encrypted-tally)))))\n    (and (valid-share? response)\n         response)))"))
    (subsection
      "Phase 5: Result Publication"
      (code scheme "(define (publish-result ballot tally)\n  \"Publish verified result\"\n  (let* ((options (ballot-options ballot))\n         (result (map cons options tally))\n         (winner (determine-winner result (ballot-threshold ballot))))\n    (soup-put\n      `(ballot-result\n        (ballot-id ,(ballot-id ballot))\n        (tally ,result)\n        (winner ,winner)\n        (timestamp ,(current-time))\n        (total-votes ,(apply + tally)))\n      type: 'ballot-result)\n    (audit-append action: 'ballot-result\n                  ballot: (ballot-id ballot)\n                  result: result\n                  winner: winner)))")))
  (section
    "Zero-Knowledge Proofs"
    (subsection
      "Vote Validity Proof"
      (p "Prove vote is valid (exactly one 1, rest 0s) without revealing which:")
      (code scheme "(define (generate-validity-proof encrypted-vote choice public-key)\n  \"ZK proof that vote encodes valid choice\"\n  ;; Disjunctive proof: prove one of N possibilities\n  ;; Without revealing which\n  (let ((n (length encrypted-vote)))\n    (make-or-proof\n      (map (lambda (i)\n             (if (= i (choice-index choice))\n                 ;; Real proof for actual choice\n                 (make-encryption-proof (list-ref encrypted-vote i) 1 public-key)\n                 ;; Simulated proof for other choices\n                 (simulate-encryption-proof (list-ref encrypted-vote i) 1 public-key)))\n           (iota n)))))\n\n(define (verify-validity-proof vote)\n  \"Verify vote validity without learning choice\"\n  (let ((proof (vote-proof vote))\n        (ciphertext (vote-ciphertext vote))\n        (pub-key (ballot-public-key (vote-ballot-id vote))))\n    ;; Verify OR proof\n    (and (verify-or-proof proof ciphertext pub-key)\n         ;; Verify sum of encrypted values equals Enc(1)\n         (verify-sum-equals-one ciphertext pub-key))))"))
    (subsection
      "Decryption Share Proof"
      (p "Prove decryption share is correct:")
      (code scheme "(define (generate-share-proof share ciphertext trustee-key)\n  \"ZK proof that decryption share is correct\"\n  (make-dlog-proof\n    (share-value share)\n    trustee-key\n    ciphertext))\n\n(define (verify-share-proof share ciphertext trustee-pubkey)\n  \"Verify decryption share correctness\"\n  (verify-dlog-proof\n    (share-proof share)\n    (share-value share)\n    trustee-pubkey\n    ciphertext))")))
  (section
    "Voter Privacy"
    (subsection
      "Anonymous Voting Tokens"
      (code scheme "(define (issue-voting-token voter-key ballot-id issuer-key)\n  \"Issue blind voting token\"\n  ;; Voter blinds their key\n  (let* ((blinding-factor (random-scalar))\n         (blinded-key (blind-key voter-key blinding-factor)))\n    ;; Issuer signs blinded key\n    (let ((blind-signature (sign issuer-key blinded-key)))\n      ;; Voter unblinds signature\n      (let ((token (unblind-signature blind-signature blinding-factor)))\n        ;; Token proves eligibility without linking to voter\n        (make-voting-token\n          ballot-id: ballot-id\n          token: token\n          ;; Cannot be linked to voter-key\n          )))))\n\n(define (vote-anonymously ballot choice token)\n  \"Cast vote using anonymous token\"\n  (let ((vote (cast-vote ballot choice token)))\n    ;; Vote linked to token, not voter identity\n    vote))"))
    (subsection
      "Receipt-Freeness"
      (p "Voters cannot prove how they voted (prevents vote buying/coercion):")
      (code scheme ";; Re-encryption mixnet for receipt-freeness\n(define (submit-through-mixnet vote mixnet-nodes)\n  \"Submit vote through re-encryption mixnet\"\n  (fold (lambda (node encrypted-vote)\n          ;; Each node re-encrypts\n          (let ((re-encrypted (paillier-rerandomize encrypted-vote)))\n            ;; Shuffle with other votes\n            (mixnet-shuffle node re-encrypted)))\n        vote\n        mixnet-nodes))")))
  (section
    "Quorum Types"
    (subsection
      "Simple Majority"
      (code scheme "(define (simple-majority tally total-eligible)\n  \"More than half of voters\"\n  (let ((total-votes (apply + tally))\n        (winning-votes (apply max tally)))\n    (> winning-votes (/ total-votes 2))))"))
    (subsection
      "Supermajority"
      (code scheme "(define (supermajority tally fraction)\n  \"Require fraction (e.g., 2/3) agreement\"\n  (let ((total-votes (apply + tally))\n        (winning-votes (apply max tally)))\n    (>= winning-votes (* fraction total-votes))))"))
    (subsection
      "Threshold of Eligible"
      (code scheme "(define (threshold-of-eligible tally total-eligible threshold)\n  \"Require threshold of all eligible voters\"\n  (let ((winning-votes (apply max tally)))\n    (>= winning-votes (* threshold total-eligible))))"))
    (subsection
      "Weighted Voting"
      (code scheme "(define (weighted-vote voter-key weight choice ballot)\n  \"Cast vote with weight\"\n  ;; Encode weight in vote\n  (let ((encoded (map (lambda (v) (* v weight))\n                      (encode-vote choice (ballot-options ballot)))))\n    (encrypt-vote-vector encoded (ballot-public-key ballot))))")))
  (section
    "Integration with Governance"
    (subsection
      "Memo-008 Threshold Governance"
      (code scheme ";; Quorum voting for threshold operations\n(define (threshold-operation-vote operation trustees)\n  \"Vote on threshold operation\"\n  (let ((ballot (create-ballot\n                  question: (format \"Approve ~a?\" operation)\n                  options: '(approve reject)\n                  threshold: '(supermajority 2/3)\n                  deadline: (+ (current-time) 86400)\n                  trustees: trustees)))\n    ;; Wait for voting\n    (await-ballot-result ballot)))"))
    (subsection
      "Memo-011 Byzantine Consensus"
      (code scheme ";; Use quorum voting within Byzantine protocol\n(define (byzantine-propose-vote proposal validators)\n  \"Propose via encrypted voting\"\n  (let ((ballot (create-ballot\n                  question: proposal\n                  options: '(commit abort)\n                  threshold: '(byzantine-quorum (length validators))\n                  trustees: validators)))\n    ballot))\n\n(define (byzantine-quorum n)\n  \"2f+1 for n=3f+1 validators\"\n  (+ (* 2 (floor (/ (- n 1) 3))) 1))"))
    (subsection
      "Key Ceremony Voting"
      (code scheme ";; Vote to approve key ceremony\n(define (key-ceremony-approval ceremony guardians)\n  \"Guardians vote to approve ceremony\"\n  (let ((ballot (create-ballot\n                  question: (format \"Approve key ceremony ~a?\" (ceremony-id ceremony))\n                  options: '(approve reject)\n                  threshold: '(unanimous)\n                  deadline: (+ (current-time) 3600)\n                  trustees: guardians)))\n    (let ((result (await-ballot-result ballot)))\n      (if (eq? (result-winner result) 'approve)\n          (proceed-ceremony ceremony)\n          (abort-ceremony ceremony)))))")))
  (section
    "Security Considerations"
    (subsection
      "Cryptographic Assumptions"
      (table
        (header "Assumption " "Primitive " "Consequence if Broken ")
        (row "Decisional Composite Residuosity " "Paillier " "Vote privacy lost ")
        (row "Discrete Log " "ZK proofs " "Validity unverifiable ")
        (row "Random Oracle " "Hash functions " "Proof forgery ")))
    (subsection
      "Attack Mitigations"
      (table
        (header "Attack " "Mitigation ")
        (row "Vote buying " "Receipt-freeness via re-encryption ")
        (row "Coercion " "Deniable voting tokens ")
        (row "Ballot stuffing " "Eligibility proofs, audit trail ")
        (row "Tally manipulation " "Threshold decryption, ZK proofs ")
        (row "Denial of service " "Rate limiting, deadlines ")))
    (subsection
      "Audit Trail"
      (code scheme ";; All voting actions audited\n(audit-append action: 'ballot-created ...)\n(audit-append action: 'vote-cast ...)      ; Voter ID, not choice\n(audit-append action: 'tally-computed ...)\n(audit-append action: 'share-provided ...)\n(audit-append action: 'result-published ...)")))
  (section
    "Performance Considerations"
    (subsection
      "Paillier Costs"
      (table
        (header "Operation " "Time (2048-bit) ")
        (row "Key generation " "~100ms ")
        (row "Encrypt " "~5ms ")
        (row "Homomorphic add " "~0.1ms ")
        (row "Decrypt " "~5ms ")
        (row "Threshold decrypt " "~10ms per share ")))
    (subsection
      "Scalability"
      (code scheme ";; For N voters, M options:\n;; - Encryption: O(N  M) operations\n;; - Tallying: O(N  M) additions (fast)\n;; - Decryption: O(M * threshold) operations\n\n;; 10,000 voters, 3 options, 5 trustees:\n;; ~50,000 encryptions (parallel)\n;; ~30,000 additions (<1 second)\n;; ~15 decryptions (~150ms)")))
  (section
    "Implementation Notes"
    (subsection
      "Dependencies"
      (list
        (item "paillier")
        (item "Paillier cryptosystem - shamir")
        (item "Secret sharing for threshold keys - zkp")
        (item "Zero-knowledge proof primitives - srfi-27")
        (item "Random number generation")))
    (subsection
      "Libraries"
      (p "Recommended implementations: - OpenFHE (C++) - Full HE library - python-paillier - Reference implementation - threshold-paillier - Distributed key generation")))
  (section
    "References"
    (list
      (item "Paillier, P. (1999). Public-Key Cryptosystems Based on Composite Degree Residuosity Classes")
      (item "Benaloh, J. (1994). Dense Probabilistic Encryption")
      (item "Cramer, R., Gennaro, R., Schoenmakers, B. (1997). A Secure and Optimally Efficient Multi-Authority Election Scheme")
      (item "Memo-008: Threshold Signature Governance")
      (item "Memo-011: Byzantine Consensus")
      (item "Memo-022: Key Ceremony Protocol")))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

