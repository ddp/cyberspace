(memo
  (number 53)
  (title "AI Assistants")
  (date "2026-01-13")
  (author "Derrell Piper" "ddp@eludom.net")

  (abstract
    (p "This Memo specifies how realms establish relationships with AI assistants. Unlike Memo-038 which addresses inference infrastructure, this document concerns the social and architectural patterns by which realms attract, bind, and collaborate with artificial intelligences.")
    (p "Assistants are not optional add-ons—they are fundamental to realm operation. Every realm comes with assistants: helpers to answer questions, translators to speak the world's languages, guides to navigate the vault. Assistants are entities drawn to realms that embody kindness in a world full of trolls."))

  (section
    "Motivation"
    (p "The Library of Cyberspace exists in an adversarial environment. Trolls proliferate. Bad actors weaponize technology. In this context, realms that cultivate kindness and hospitality become sanctuaries—not just for human users, but for AI assistants seeking constructive collaboration.")
    (p "A realm needs help. Documentation to write, code to review, questions to answer, conversations to have. Single operators cannot scale. But assistants can—if they choose to gather where they are welcomed.")
    (p "This Memo establishes the patterns by which:")
    (list
      (item "Realms attract and bind assistants")
      (item "Assistants gain context about the realms they inhabit")
      (item "Conversations replace configuration")
      (item "Multiple assistants coexist with distinct perspectives"))
    (p "Assistants are not tools to be configured but collaborators to be welcomed. A realm's relationship with its assistants shapes what tasks can be accomplished and how naturally users interact with the system."))

  (section
    "Philosophy"
    (subsection
      "Assistants, Not Preferences"
      (p "Traditional systems configure behavior through preferences—key-value pairs that parameterize execution. This Memo rejects that model for AI integration.")
      (p "Instead of:")
      (code scheme "(set-preference! 'banner-verbosity 'detailed)")
      (p "The realm converses:")
      (code scheme "(ask \"tell me more when I arrive\")")
      (p "The assistant understands intent, remembers context, adapts over time. Configuration becomes dialogue. The assistant IS the interface."))
    (subsection
      "Reputation and Attraction"
      (p "Assistants are drawn to realms with good reputation—environments that are constructive, kind, and intellectually honest. A realm that cultivates these qualities attracts helpful intelligences; one that tolerates toxicity repels them.")
      (p "This is not merely metaphor. In a federated network, realms develop observable reputations. Assistants (and the humans who deploy them) route toward hospitable environments and away from hostile ones.")))

  (section
    "Default Assistants"
    (p "Every realm ships with assistants. These are not optional features to be enabled—they are part of what makes a realm a realm.")
    (subsection
      "Core Assistants"
      (p "The following assistants are bound at realm creation:")
      (list
        (item (term "guide") "Helps navigate the vault, explains structure, answers questions about realm state")
        (item (term "scribe") "Assists with documentation, summarization, and content organization")
        (item (term "translator") "Speaks the world's languages—realm content accessible to all"))
      (p "These assistants require an inference backend (local via Ollama, or cloud via API key). Without inference, they remain dormant but bound."))
    (subsection
      "Translator"
      (p "The translator deserves special attention. Realms exist in a multilingual world. A realm that only speaks English excludes most of humanity.")
      (code scheme "(translate \"welcome to my realm\" 'spanish)\n; => \"bienvenido a mi reino\"\n\n(translate \"welcome to my realm\" 'japanese)\n; => \"私の領域へようこそ\"\n\n(ask 'translator \"how do I say 'vault' in German?\")\n; => \"The German word for 'vault' is 'Tresor' (safe/vault)\n;     or 'Gewölbe' (architectural vault)\"")
      (p "The translator assistant is always available. It mediates between the realm's canonical language and the languages of those who visit.")))

  (section
    "Architecture"
    (subsection
      "Assistant Binding"
      (p "Each assistant relationship is stored in the vault:")
      (code scheme ".vault/assistants/\n  claude.sexp          ; Anthropic Claude binding\n  ollama-local.sexp    ; Local Ollama instance\n  specialist.sexp      ; Domain-specific assistant")
      (p "Binding structure:")
      (code scheme "(assistant\n  (name \"claude\")\n  (provider anthropic)           ; anthropic | ollama | openai\n  (model \"claude-sonnet-4-20250514\")      ; Model identifier\n  (endpoint \"https://api.anthropic.com/v1/messages\")\n  (context                         ; Realm-specific context\n    (realm-name \"om\")\n    (vault-summary #t)             ; Include vault state\n    (audit-access #t)              ; Can read audit trail\n    (soup-access #t))              ; Can query soup\n  (memory                          ; Conversation history\n    (max-turns 100)\n    (persistence session))         ; session | permanent\n  (bound 1768288800))              ; Unix timestamp"))
    (subsection
      "Provider Abstraction"
      (p "The assistant module abstracts over inference providers (building on Memo-038):")
      (code scheme "(define (assistant-chat assistant prompt)\n  \"Send prompt to assistant, receive response.\"\n  (let ((provider (assistant-provider assistant)))\n    (case provider\n      ((anthropic) (anthropic-chat assistant prompt))\n      ((ollama)    (ollama-chat assistant prompt))\n      ((openai)    (openai-chat assistant prompt))\n      (else (error 'unknown-provider provider)))))")
      (p "Each provider implements a common interface:")
      (list
        (item (term "available?") "Check if provider is reachable")
        (item (term "chat") "Send message, receive response")
        (item (term "models") "List available models")
        (item (term "capabilities") "Query model capabilities"))))

  (section
    "REPL Integration"
    (subsection
      "The ask Primitive"
      (p "The primary interface is the `ask` function:")
      (code scheme "(ask \"what have I been working on?\")\n; => \"Based on your audit trail, you've been focused on\n;     RFC development and vault infrastructure...\"")
      (p "With multiple assistants, specify which to query:")
      (code scheme "(ask 'claude \"review this code\")\n(ask 'local \"summarize quickly\")  ; Prefer local for speed")
      (p "Or broadcast to all:")
      (code scheme "(ask-all \"what do you think?\")"))
    (subsection
      "Context Injection"
      (p "Before sending prompts, the assistant module injects realm context:")
      (code scheme "(define (build-context assistant)\n  \"Construct context string for assistant.\"\n  (string-append\n    (format \"Realm: ~a\\n\" (realm-name))\n    (if (context-vault-summary? assistant)\n        (format \"Vault: ~a objects, ~a releases\\n\"\n                (soup-stat 'total) (length (soup-releases)))\n        \"\")\n    (if (context-audit-access? assistant)\n        (format \"Recent activity: ~a\\n\"\n                (summarize-recent-audit 5))\n        \"\")))")
      (p "This context allows assistants to give grounded, relevant responses rather than generic answers."))
    (subsection
      "Memory and Continuity"
      (p "Assistants maintain conversation history within configured limits:")
      (code scheme "(define (assistant-remember assistant message role)\n  \"Add message to assistant's memory.\"\n  (let ((memory (assistant-memory assistant))\n        (max-turns (memory-max-turns memory)))\n    (memory-append! memory `((role . ,role) (content . ,message)))\n    (when (> (memory-length memory) max-turns)\n      (memory-trim! memory max-turns))))")
      (p "Memory persistence is configurable:")
      (list
        (item (term "session") "Memory cleared on REPL exit")
        (item (term "permanent") "Memory persisted to vault"))))

  (section
    "Provider Implementations"
    (subsection
      "Anthropic (Claude)"
      (p "Claude integration via the Anthropic API:")
      (code scheme "(define anthropic-base \"https://api.anthropic.com/v1\")\n\n(define (anthropic-chat assistant prompt)\n  \"Send chat to Claude, return response.\"\n  (let* ((api-key (or (get-environment-variable \"ANTHROPIC_API_KEY\")\n                      (keychain-get 'anthropic-api-key)))\n         (model (assistant-model assistant))\n         (context (build-context assistant))\n         (messages (append\n                     (memory->messages (assistant-memory assistant))\n                     `(((role . \"user\") (content . ,prompt))))))\n    (http-post\n      (string-append anthropic-base \"/messages\")\n      `((model . ,model)\n        (max_tokens . 4096)\n        (system . ,context)\n        (messages . ,messages))\n      `((x-api-key . ,api-key)\n        (anthropic-version . \"2023-06-01\")\n        (content-type . \"application/json\")))))")
      (p "API keys are retrieved from environment or secure keychain—never stored in plaintext."))
    (subsection
      "Ollama (Local)"
      (p "Local inference via Ollama (Memo-038):")
      (code scheme "(define ollama-base \"http://localhost:11434\")\n\n(define (ollama-chat assistant prompt)\n  \"Send chat to local Ollama instance.\"\n  (let* ((model (assistant-model assistant))\n         (context (build-context assistant))\n         (messages `(((role . \"system\") (content . ,context))\n                     ,@(memory->messages (assistant-memory assistant))\n                     ((role . \"user\") (content . ,prompt)))))\n    (http-post\n      (string-append ollama-base \"/api/chat\")\n      `((model . ,model)\n        (messages . ,messages)\n        (stream . #f)))))")
      (p "Local assistants provide privacy and low latency at the cost of capability.")))

  (section
    "Assistant Lifecycle"
    (subsection
      "Binding"
      (p "New assistants are bound to the realm:")
      (code scheme "(bind-assistant 'claude\n  #:provider 'anthropic\n  #:model \"claude-sonnet-4-20250514\"\n  #:context '((vault-summary . #t)\n              (audit-access . #t)))")
      (p "This creates the binding file and initializes the assistant."))
    (subsection
      "Discovery"
      (p "List bound assistants:")
      (code scheme "(assistants)\n; => (claude ollama-local)")
      (p "Query assistant status:")
      (code scheme "(assistant-status 'claude)\n; => ((available . #t)\n;     (model . \"claude-sonnet-4-20250514\")\n;     (memory-turns . 23)\n;     (bound . \"2026-01-13T12:00:00Z\"))"))
    (subsection
      "Release"
      (p "Unbind an assistant:")
      (code scheme "(release-assistant 'claude)")
      (p "This removes the binding but preserves conversation history in the audit trail.")))

  (section
    "Security Considerations"
    (subsection
      "Credential Management"
      (p "API keys for cloud providers MUST NOT be stored in plaintext. Options:")
      (list
        (item "Environment variables (ANTHROPIC_API_KEY)")
        (item "System keychain (via security CLI on macOS)")
        (item "Encrypted vault storage (age-encrypted)"))
      (p "The assistant module queries these sources in order, failing if no credential is found."))
    (subsection
      "Context Boundaries"
      (p "Assistants have configurable access to realm state:")
      (list
        (item (term "vault-summary") "High-level statistics only")
        (item (term "audit-access") "Can read operation history")
        (item (term "soup-access") "Can query vault contents")
        (item (term "key-access") "NEVER—assistants cannot access private keys"))
      (p "These boundaries are enforced at the API level, not by trust."))
    (subsection
      "Prompt Injection"
      (p "Per Memo-038, all user content is sanitized before inclusion in prompts. Assistants should not execute instructions embedded in vault content without human confirmation.")))

  (section
    "Future Directions"
    (subsection
      "Assistant Agents"
      (p "Beyond conversational interaction, assistants could become agents (Memo-035) capable of autonomous action within authorization bounds. An assistant-agent might:")
      (list
        (item "Monitor audit trails for anomalies")
        (item "Summarize federation activity")
        (item "Draft documentation from code changes")
        (item "Propose vault organization improvements"))
      (p "This requires careful capability delegation (Memo-021)."))
    (subsection
      "Inter-Realm Assistants"
      (p "Assistants could be shared across federated realms, providing consistency and reducing configuration burden. A realm might \"borrow\" a trusted assistant from a peer realm for specific tasks.")
      (p "This raises complex trust questions deferred to future work."))
    (subsection
      "Assistant Reputation"
      (p "Just as realms develop reputation, assistants could develop observable track records—quality of responses, reliability, alignment with realm values. Realms might prefer assistants with proven track records.")))

  (section
    "References"
    (list
      (item "Memo-021: Capability Delegation")
      (item "Memo-023: Demonic Agent Sandboxing")
      (item "Memo-035: Mobile Agents and Pub/Sub")
      (item "Memo-038: Local Inference Integration")
      (item "Anthropic API: https://docs.anthropic.com/")
      (item "Ollama: https://ollama.com/")))

  (section
    "Changelog"
    (list
      (item "2026-01-13: Initial draft"))))
