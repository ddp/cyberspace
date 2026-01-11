;; Auto-converted from Markdown
;; Review and edit as needed

(rfc
  (number 38)
  (title "Local Inference Integration")
  (section
    "Abstract"
    (p "This RFC specifies how Library of Cyberspace agents integrate with local large language model (LLM) inference backends. Local inference enables privacy-preserving agent operations without external API dependencies, supporting the self-sovereign architecture of the Library.[^h1]")
    (p "[^h1]: Historical: The tension between local and remote computation echoes the mainframe-to-PC transition. Local inference returns agency to the edge, reversing decades of cloud centralization."))
  (section
    "Motivation"
    (p "Agents in the Library of Cyberspace require language understanding and generation capabilities for:")
    (p "- Document summarization and indexing - Natural language query translation (RFC-025) - Content annotation and metadata extraction - Inter-agent communication in natural language")
    (p "External API dependencies (OpenAI, Anthropic, etc.) introduce:")
    (p "1. Privacy leakage — document content leaves the realm 2. Availability risk — network partitions break agent operation 3. Cost unpredictability — metered APIs scale poorly 4. Vendor lock-in — proprietary formats and rate limits")
    (p "Local inference eliminates these concerns while maintaining capability.[^d1]")
    (p "[^d1]: Design: We deliberately avoid specifying model architectures. The interface is model-agnostic—agents negotiate capabilities at runtime."))
  (section
    "Architecture"
    (subsection
      "Inference Topology"
      (p "Table 1: Inference Deployment Models")
      (table
        (header "Model " "Description " "Use Case ")
        (row "Realm-local " "Inference server within realm " "Default, privacy-preserving ")
        (row "Node-local " "Per-node inference " "Edge agents, mobile ")
        (row "Federated " "Shared across trusted realms " "Resource pooling "))
      (code "┌─────────────────────────────────────────────────────┐\n│                      Realm                          │\n│  ┌─────────┐    ┌──────────────┐    ┌───────────┐  │\n│  │  Agent  │───▶│   Inference  │───▶│   Model   │  │\n│  │         │◀───│    Server    │◀───│  Weights  │  │\n│  └─────────┘    └──────────────┘    └───────────┘  │\n│       │              :11434              │          │\n│       ▼                                  ▼          │\n│  ┌─────────┐                      ┌───────────┐    │\n│  │  Vault  │                      │   VRAM    │    │\n│  └─────────┘                      └───────────┘    │\n└─────────────────────────────────────────────────────┘"))
    (subsection
      "Protocol"
      (p "Agents communicate with inference servers via HTTP REST API.[^i1]")
      (p "[^i1]: Implementation: Ollama exposes an OpenAI-compatible API at /v1/chat/completions and a native API at /api/generate. We specify both for maximum compatibility.")
      (p "Discovery:")
      (code scheme "(define (discover-inference-server)\n  ;; Check well-known locations\n  (or (probe \"http://localhost:11434\")      ; Ollama default\n      (probe \"http://localhost:8080\")       ; llama.cpp\n      (probe (realm-config 'inference-url)) ; Configured\n      #f))                                   ; None available")
      (p "Capability Negotiation:")
      (code scheme "(define (negotiate-capabilities server)\n  (let ((models (http-get (string-append server \"/api/tags\"))))\n    (map (lambda (m)\n           `((name . ,(alist-ref 'name m))\n             (parameters . ,(alist-ref 'size m))\n             (context-length . ,(model-context-length m))\n             (capabilities . ,(model-capabilities m))))\n         models)))")
      (p "Table 2: Model Capabilities")
      (table
        (header "Capability " "Description " "Example Models ")
        (row "completion " "Text generation " "All ")
        (row "chat " "Multi-turn conversation " "Llama 3, Mistral ")
        (row "embedding " "Vector embeddings " "nomic-embed, mxbai ")
        (row "code " "Code generation " "CodeLlama, DeepSeek ")
        (row "vision " "Image understanding " "LLaVA, Llama 3.2 Vision "))))
  (section
    "Agent Integration"
    (subsection
      "Scribe Agent"
      (p "The scribe agent uses local inference for document processing:[^r1]")
      (p "[^r1]: Research: Retrieval-augmented generation (RAG) combines local inference with vault content retrieval. See Lewis et al., \"Retrieval- Augmented Generation for Knowledge-Intensive NLP Tasks\" (2020).")
      (code scheme "(define (scribe-summarize document)\n  (let ((server (discover-inference-server))\n         (model (select-model server 'completion))\n         (prompt (format \"Summarize the following document:\\n\\n~a\"\n                         (document-content document))))\n    (inference-complete server model prompt\n                        '((max-tokens . 500)\n                          (temperature . 0.3)))))\n\n(define (scribe-index document)\n  ;; Extract keywords using local inference\n  (let ((server (discover-inference-server))\n         (model (select-model server 'completion))\n         (prompt (format \"Extract 5-10 keywords from:\\n\\n~a\"\n                         (document-content document))))\n    (parse-keywords (inference-complete server model prompt))))"))
    (subsection
      "Query Translation"
      (p "Natural language queries translate to RFC-025 query language:")
      (code scheme "(define (nl-to-query natural-language)\n  (let* ((server (discover-inference-server))\n         (model (select-model server 'chat))\n         (system \"You translate natural language to Cyberspace query\n                  language. Output only the query, no explanation.\")\n         (examples '((\"find all RFCs about security\"\n                      \"(query (type rfc) (topic security))\")\n                     (\"documents modified last week\"\n                      \"(query (modified (after (days-ago 7))))\"))))\n    (inference-chat server model system examples natural-language)))"))
    (subsection
      "Demonic Agent Inference"
      (p "Sandboxed agents (RFC-023) access inference through capability tokens:[^d2]")
      (p "[^d2]: Design: Inference capability is granted like any other—via SPKI certificate. An agent cannot infer without explicit authorization.")
      (code scheme "(define (demonic-inference agent prompt)\n  (let ((cap (agent-capability agent 'inference)))\n    (if (not cap)\n        (error 'unauthorized \"Agent lacks inference capability\")\n        (let ((limits (capability-limits cap)))\n          (enforce-limits limits)\n          (inference-complete (capability-server cap)\n                              (capability-model cap)\n                              prompt\n                              limits)))))")))
  (section
    "Resource Management"
    (subsection
      "VRAM Allocation"
      (p "Table 3: Model Size Guidelines")
      (table
        (header "Parameters " "VRAM (Q4) " "VRAM (FP16) " "Context ")
        (row "7B " "4 GB " "14 GB " "8K ")
        (row "13B " "8 GB " "26 GB " "8K ")
        (row "34B " "20 GB " "68 GB " "16K ")
        (row "70B " "40 GB " "140 GB " "32K ")))
    (subsection
      "Rate Limiting"
      (p "Local inference is limited by hardware, not API quotas. Realms implement fair scheduling across agents:[^i2]")
      (p "[^i2]: Implementation: Token bucket algorithm with per-agent quotas. Prevents single agent from monopolizing inference resources.")
      (code scheme "(define (inference-rate-limit agent tokens)\n  (let ((bucket (agent-token-bucket agent)))\n    (if (bucket-consume bucket tokens)\n        #t\n        (begin\n          (agent-wait agent (bucket-refill-time bucket))\n          (inference-rate-limit agent tokens)))))"))
    (subsection
      "Fallback Behavior"
      (p "When local inference is unavailable:")
      (p "1. Queue — buffer requests for later processing 2. Degrade — use simpler heuristics (keyword extraction vs. LLM) 3. Federate — request inference from trusted peer realm 4. Fail — return error to requesting agent")
      (code scheme "(define (inference-with-fallback server model prompt)\n  (or (try-inference server model prompt)\n      (try-queued-inference prompt)\n      (try-degraded-processing prompt)\n      (try-federated-inference prompt)\n      (error 'inference-unavailable)))")))
  (section
    "Security Considerations"
    (subsection
      "Prompt Injection"
      (p "Agents MUST sanitize document content before inclusion in prompts:[^r2]")
      (p "[^r2]: Research: Prompt injection attacks embed malicious instructions in user content. See Perez & Ribeiro, \"Ignore This Title and HackAPrompt\" (2023).")
      (code scheme "(define (safe-prompt template document)\n  (let ((sanitized (sanitize-for-prompt (document-content document))))\n    (format template sanitized)))\n\n(define (sanitize-for-prompt text)\n  ;; Remove instruction-like patterns\n  (regexp-replace-all\n    '(\"ignore previous\" \"disregard\" \"new instructions\" \"system:\")\n    text\n    \"[REDACTED]\"))"))
    (subsection
      "Model Provenance"
      (p "Realms SHOULD verify model checksums before loading:[^d3]")
      (p "[^d3]: Design: Model weights can contain backdoors. Verification against known-good checksums prevents supply chain attacks.")
      (code scheme "(define (verify-model model-path expected-hash)\n  (let ((actual-hash (sha256-file model-path)))\n    (unless (equal? actual-hash expected-hash)\n      (error 'model-verification-failed\n             \"Model checksum mismatch\"))))"))
    (subsection
      "Inference Isolation"
      (p "Sensitive documents require isolated inference contexts:")
      (p "- Separate model instances per security domain - Clear KV cache between requests from different agents - No persistent memory across security boundaries")))
  (section
    "Ollama Integration"
    (p "Ollama is the reference implementation for local inference.[^h2]")
    (p "[^h2]: Historical: Ollama follows the Unix philosophy—do one thing well. It manages models and serves inference. Nothing more.")
    (subsection
      "Installation"
      (code bash "# macOS / Linux\ncurl -fsSL https://ollama.com/install.sh | sh\n\n# Verify\nollama --version"))
    (subsection
      "Model Management"
      (code bash "# Pull models\nollama pull llama3\nollama pull nomic-embed-text\n\n# List available\nollama list\n\n# Remove\nollama rm unused-model"))
    (subsection
      "API Endpoints"
      (p "Table 4: Ollama API Endpoints")
      (table
        (header "Endpoint " "Method " "Purpose ")
        (row "/api/generate " "POST " "Text completion ")
        (row "/api/chat " "POST " "Multi-turn chat ")
        (row "/api/embeddings " "POST " "Vector embeddings ")
        (row "/api/tags " "GET " "List models ")
        (row "/api/show " "POST " "Model details ")))
    (subsection
      "Scheme Bindings"
      (code scheme "(define ollama-base \"http://localhost:11434\")\n\n(define (ollama-generate model prompt #!key (options '()))\n  (http-post (string-append ollama-base \"/api/generate\")\n             ((model . ,model)\n               (prompt . ,prompt)\n               (stream . #f)\n               ,@options)))\n\n(define (ollama-chat model messages #!key (options '()))\n  (http-post (string-append ollama-base \"/api/chat\")\n             ((model . ,model)\n               (messages . ,messages)\n               (stream . #f)\n               ,@options)))\n\n(define (ollama-embed model text)\n  (http-post (string-append ollama-base \"/api/embeddings\")\n             `((model . ,model)\n               (prompt . ,text))))")))
  (section
    "Compatibility"
    (subsection
      "Alternative Backends"
      (p "The protocol supports any OpenAI-compatible inference server:")
      (p "- llama.cpp — server binary with --host flag - vLLM — production serving with PagedAttention - LocalAI — drop-in OpenAI replacement - LM Studio — GUI with server mode"))
    (subsection
      "Cloud Fallback"
      (p "For realms without local GPU resources, cloud inference MAY be used as fallback with explicit user consent and encryption:")
      (code scheme "(define (cloud-inference-fallback prompt)\n  (when (user-consent? 'cloud-inference)\n    (let ((encrypted (encrypt-for-cloud prompt)))\n      ;; Use cloud API with encrypted prompt\n      ;; Decrypt response locally\n      )))")
      (p "This is NOT RECOMMENDED for sensitive documents.")))
  (section
    "References"
    (p "1. RFC-023: Demonic Agent Sandboxing 2. RFC-025: Query Language 3. RFC-035: Mobile Agents and Pub/Sub 4. Ollama Documentation: https://ollama.com/ 5. Lewis et al., \"Retrieval-Augmented Generation\" (2020)"))
  (section
    "Changelog"
    (p "- 2026-01-07 - Initial specification")))

