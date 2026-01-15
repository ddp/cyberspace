;; Memo-059: Lazy Discovery
;; Reactive change propagation in the weave

(memo
  (number 57)
  (title "Lazy Discovery")
  (status "Draft")
  (date "January 2026")
  (author "Derrell Piper" "ddp@archlinux.us")

  (section
    "Abstract"
    (p "Defines a reactive layer for the weave where realms lazily discover changes forged elsewhere. Complements the active forge model with pubsub semantics over gossip."))

  (section
    "1. Motivation"
    (p "The forge model requires active participation: realms compile, seal, sign, and gossip propagates results. But realms also need to know when peers have forged something new without polling.")
    (p "Lazy discovery adds subscription semantics. Realms express interest; the weave notifies them. Pull when interested, ignore when not."))

  (section
    "2. Subscription Model"

    (subsection
      "2.1 Interest Expression"
      (p "Realms subscribe to change feeds:")
      (code scheme "(subscribe realm: 'fluffy)           ; all changes from fluffy
(subscribe key: hash)                 ; changes to specific object
(subscribe topic: 'rfc)               ; semantic topic
(subscribe pattern: \"spki/scheme/*\") ; glob pattern")
      (p "Subscriptions are SPKI certificates - signed expressions of interest that can be delegated and revoked."))

    (subsection
      "2.2 Notification Format"
      (p "Change notifications are lightweight:")
      (code scheme "(change
  (realm fluffy)
  (lamport 42)
  (hash \"sha512:...\")
  (type sealed-archive)
  (topic rfc)
  (signature ...))")
      (p "Notifications announce existence, not content. Interested realms pull the object via normal gossip.")))

  (section
    "3. Gossip as Tala"
    (p "In Indian classical music, tala is the rhythmic cycle underlying the raga. Without tala, the melody has no structure. Without gossip, the weave has no coherence.")
    (p "Gossip is the tala of cyberspace - the steady beat that carries forge and discovery alike. Realms may create in isolation, but the rhythm connects them."))

  (section
    "4. Gossip Integration"

    (subsection
      "4.1 Notification Propagation"
      (p "Change notifications piggyback on gossip protocol (Memo-010). They are small, signed, and expire:")
      (list
        (item "Notifications included in gossip heartbeat")
        (item "TTL limits propagation (default: 24 hours)")
        (item "Deduplication by (realm, lamport, hash) tuple")))

    (subsection
      "4.2 Request on Interest"
      (p "When a notification matches a subscription:")
      (code scheme "(on-change notification
  (when (matches-subscription? notification subscriptions)
    (request-object (change-hash notification) (change-realm notification))))")
      (p "The request is lazy - realms may defer, batch, or ignore based on priority.")))

  (section
    "5. Subscription Certificates"

    (subsection
      "5.1 Structure"
      (code scheme "(cert
  (issuer realm-key)
  (subject subscription)
  (validity (not-after \"2026-12-31\"))
  (delegate #f)
  (signature ...))")
      (p "Subscriptions are first-class objects in the SPKI model. They can be stored in vaults, shared, and audited."))

    (subsection
      "5.2 Privacy Considerations"
      (p "Subscriptions reveal interest. Realms may:")
      (list
        (item "Subscribe through intermediaries")
        (item "Use broad patterns to obscure specific interest")
        (item "Accept latency for privacy (poll instead of subscribe)"))))

  (section
    "6. Implementation"

    (subsection
      "6.1 Subscription Registry"
      (code scheme "(define *subscriptions* '())

(define (subscribe #!key realm key topic pattern)
  \"Register interest in changes.\"
  (let ((sub (make-subscription realm: realm key: key
                                topic: topic pattern: pattern)))
    (set! *subscriptions* (cons sub *subscriptions*))
    (announce-subscription sub)
    sub))

(define (unsubscribe sub)
  \"Revoke interest.\"
  (set! *subscriptions* (remove sub *subscriptions*))
  (announce-revocation sub))"))

    (subsection
      "6.2 Change Emission"
      (code scheme "(define (emit-change object)
  \"Announce a newly forged object.\"
  (let ((notification (make-change-notification
                        realm: *current-realm*
                        lamport: (lamport-time)
                        hash: (object-hash object)
                        type: (object-type object)
                        topic: (object-topic object))))
    (sign-and-gossip notification)))")))

  (section
    "7. Relationship to Forge"
    (p "Lazy discovery complements, not replaces, the forge:")
    (code "Forge:     Active. You create, you seal, you sign.
Discovery: Reactive. You express interest, you're notified.
Gossip:    Transport. Carries both forged objects and notifications.")
    (p "The weave remains a system of forges. Lazy discovery is how forges hear about each other's work."))

  (section
    "8. Security Considerations"
    (list
      (item "Notification spam: Rate limiting per realm (Memo-032)")
      (item "Subscription flooding: Quota on active subscriptions")
      (item "Privacy leakage: Subscriptions reveal interest graphs")
      (item "Replay attacks: Lamport ordering prevents stale notifications")))

  (section
    "References"
    (references
      (ref "Memo-010" "2026" "Federation Protocol")
      (ref "Memo-012" "2026" "Lamport Clocks")
      (ref "Memo-032" "2026" "Rate Limiting")
      (ref "Memo-004" "2026" "SPKI Authorization"))))
