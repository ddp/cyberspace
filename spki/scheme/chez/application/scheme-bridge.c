/*
 * scheme-bridge.c - Chez Scheme native bridge implementation
 */

#include "scheme-bridge.h"
#include <scheme.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

static bool initialized = false;

bool scheme_init(int argc, char **argv) {
    if (initialized) return true;

    fprintf(stderr, "[scheme-bridge] Sscheme_init...\n");
    Sscheme_init(NULL);

    // Use bundled boot files from app Resources
    // If running from app bundle, use Resources/boot/*.boot
    // Otherwise fall back to Homebrew installation
    char boot_path[1024];
    char *resources_path = getenv("RESOURCEPATH");
    if (resources_path) {
        snprintf(boot_path, sizeof(boot_path), "%s/boot/petite.boot", resources_path);
        fprintf(stderr, "[scheme-bridge] Registering: %s\n", boot_path);
        Sregister_boot_file(boot_path);
        snprintf(boot_path, sizeof(boot_path), "%s/boot/scheme.boot", resources_path);
        fprintf(stderr, "[scheme-bridge] Registering: %s\n", boot_path);
        Sregister_boot_file(boot_path);
    } else {
        fprintf(stderr, "[scheme-bridge] Using Homebrew boot files\n");
        Sregister_boot_file("/opt/homebrew/Cellar/chezscheme/10.3.0/lib/csv10.3.0/tarm64osx/petite.boot");
        Sregister_boot_file("/opt/homebrew/Cellar/chezscheme/10.3.0/lib/csv10.3.0/tarm64osx/scheme.boot");
    }

    fprintf(stderr, "[scheme-bridge] Sbuild_heap...\n");
    Sbuild_heap(NULL, NULL);
    fprintf(stderr, "[scheme-bridge] Heap built OK\n");

    // Load REPL helpers into interaction environment
    const char *repl_init =
        "; Cyberspace modules list\n"
        "(define *cyberspace-modules*\n"
        "  '(\"crypto-ffi\" \"sexp\" \"capability\" \"fips\" \"audit\" \"wordlist\"\n"
        "    \"bloom\" \"catalog\" \"keyring\" \"cert\" \"enroll\" \"gossip\" \"security\"\n"
        "    \"vault\" \"auto-enroll\" \"inspector\" \"display\" \"filetype\" \"forum\"\n"
        "    \"http\" \"info\" \"mpe\" \"pencil\" \"repl\" \"scrutinizer\" \"server\"))\n"
        "\n"
        "; Analyze source file for LOC/lambda metrics\n"
        "(define (analyze-source src-file)\n"
        "  (if (not (file-exists? src-file))\n"
        "      '((loc . 0) (lambdas . 0) (loc/lambda . 0))\n"
        "      (call-with-input-file src-file\n"
        "        (lambda (port)\n"
        "          (let loop ((loc 0) (lambdas 0))\n"
        "            (let ((line (get-line port)))\n"
        "              (if (eof-object? line)\n"
        "                  (let ((ratio (if (> lambdas 0) (div loc lambdas) 0)))\n"
        "                    `((loc . ,loc) (lambdas . ,lambdas) (loc/lambda . ,ratio)))\n"
        "                  (let* ((trimmed (string-trim-both line))\n"
        "                         (is-blank (string=? trimmed \"\"))\n"
        "                         (is-comment (and (> (string-length trimmed) 0)\n"
        "                                          (char=? (string-ref trimmed 0) #\\;)))\n"
        "                         (has-define (string-contains line \"(define \"))\n"
        "                         (has-lambda (string-contains line \"(lambda \")))\n"
        "                    (loop (if (or is-blank is-comment) loc (+ loc 1))\n"
        "                          (+ lambdas\n"
        "                             (if has-define 1 0)\n"
        "                             (if has-lambda 1 0)))))))))))\n"
        "\n"
        "; String utilities for Chez\n"
        "(define (string-trim-both s)\n"
        "  (let* ((len (string-length s))\n"
        "         (start (let loop ((i 0))\n"
        "                  (if (or (= i len) (not (char-whitespace? (string-ref s i))))\n"
        "                      i (loop (+ i 1)))))\n"
        "         (end (let loop ((i (- len 1)))\n"
        "                (if (or (< i start) (not (char-whitespace? (string-ref s i))))\n"
        "                    (+ i 1) (loop (- i 1))))))\n"
        "    (substring s start end)))\n"
        "\n"
        "(define (string-contains str substr)\n"
        "  (let ((slen (string-length str))\n"
        "        (sslen (string-length substr)))\n"
        "    (let loop ((i 0))\n"
        "      (cond ((> (+ i sslen) slen) #f)\n"
        "            ((string=? (substring str i (+ i sslen)) substr) i)\n"
        "            (else (loop (+ i 1)))))))\n"
        "\n"
        "; SICP metrics analyzer\n"
        "(define (sicp)\n"
        "  (guard (exn [else (display \"Error in sicp: \")\n"
        "                    (display exn)\n"
        "                    (newline)\n"
        "                    (flush-output-port (current-output-port))])\n"
        "    (display \"\\nSICP Metrics - spki/scheme\\n\\n\")\n"
        "    (flush-output-port (current-output-port))\n"
        "    (let* ((resources (getenv \"RESOURCEPATH\"))\n"
        "           (lib-path (if resources\n"
        "                         (string-append resources \"/lib/cyberspace/\")\n"
        "                         \"lib/cyberspace/\")))\n"
        "    (let loop ((modules *cyberspace-modules*)\n"
        "               (total-loc 0)\n"
        "               (total-lambdas 0))\n"
        "      (if (null? modules)\n"
        "          (begin\n"
        "            (display \"\\n  ─────────────────────────────────\\n\")\n"
        "            (printf \"  Σ ~a LOC · ~a λ · ~a LOC/λ\\n\\n\"\n"
        "                    total-loc total-lambdas\n"
        "                    (if (> total-lambdas 0) (div total-loc total-lambdas) 0))\n"
        "            (flush-output-port (current-output-port)))\n"
        "          (let* ((mod (car modules))\n"
        "                 (src (string-append lib-path mod \".sls\"))\n"
        "               (metrics (analyze-source src))\n"
        "               (loc (cdr (assq 'loc metrics)))\n"
        "               (lambdas (cdr (assq 'lambdas metrics)))\n"
        "               (ratio (cdr (assq 'loc/lambda metrics))))\n"
        "          (when (> loc 0)\n"
        "            (let ((padded (string-append mod (make-string (max 0 (- 12 (string-length mod))) #\\space))))\n"
        "              (printf \"  ~a: ~a LOC · ~a λ · ~a LOC/λ\\n\"\n"
        "                      padded loc lambdas ratio)))\n"
        "              (loop (cdr modules)\n"
        "                    (+ total-loc loc)\n"
        "                    (+ total-lambdas lambdas))))))\n"
        "    (void)))\n"
        "\n"
        "(define (help)\n"
        "  (guard (exn [else (display \"Error in help: \")\n"
        "                    (display exn)\n"
        "                    (newline)\n"
        "                    (flush-output-port (current-output-port))])\n"
        "    (display \"Available commands:\\n\\n\")\n"
        "    (flush-output-port (current-output-port))\n"
        "    (display \"Core:\\n\")\n"
        "    (display \"  (sicp)           - Analyze SICP metrics for all modules\\n\")\n"
        "    (display \"  (help)           - This message\\n\")\n"
        "    (display \"  (version)        - Show version info\\n\\n\")\n"
        "    (flush-output-port (current-output-port))\n"
        "    (display \"Vault:\\n\")\n"
        "    (display \"  (vault-status)   - Show vault status\\n\")\n"
        "    (display \"  (vault-path)     - Show vault path\\n\")\n"
        "    (display \"  (catalog)        - List vault contents\\n\\n\")\n"
        "    (flush-output-port (current-output-port))\n"
        "    (display \"Crypto:\\n\")\n"
        "    (display \"  (keygen)         - Generate key pair\\n\")\n"
        "    (display \"  (sign data)      - Sign data\\n\")\n"
        "    (display \"  (verify sig)     - Verify signature\\n\\n\")\n"
        "    (flush-output-port (current-output-port))\n"
        "    (display \"SPKI:\\n\")\n"
        "    (display \"  (make-cert ...)  - Create certificate\\n\")\n"
        "    (display \"  (verify-cert c)  - Verify certificate\\n\")\n"
        "    (flush-output-port (current-output-port))\n"
        "    (void)))\n"
        "\n"
        "(define (version)\n"
        "  (display \"Library of Cyberspace v0.9.12\\n\")\n"
        "  (display \"Chez Scheme REPL\\n\"))\n"
        "\n"
        "(define (novice)\n"
        "  (display \"Switched to novice mode\\n\"))\n"
        "\n"
        "(define (schemer)\n"
        "  (display \"Switched to schemer mode\\n\"))\n"
        "\n"
        "(define (module-summary)\n"
        "  (guard (exn [else (display \"Error in module-summary: \")\n"
        "                    (display exn)\n"
        "                    (newline)])\n"
        "    (let* ((resources (getenv \"RESOURCEPATH\"))\n"
        "           (lib-path (if resources\n"
        "                         (string-append resources \"/lib/cyberspace/\")\n"
        "                         \"lib/cyberspace/\")))\n"
        "      (let loop ((modules *cyberspace-modules*)\n"
        "                 (total-loc 0)\n"
        "                 (total-lambdas 0))\n"
        "        (if (null? modules)\n"
        "            (begin\n"
        "              (printf \"Total: ~a modules, ~a LOC, ~a λ, ~a LOC/λ\\n\"\n"
        "                      (length *cyberspace-modules*)\n"
        "                      total-loc\n"
        "                      total-lambdas\n"
        "                      (if (> total-lambdas 0) (div total-loc total-lambdas) 0))\n"
        "              (void))\n"
        "            (let* ((mod (car modules))\n"
        "                   (src (string-append lib-path mod \".sls\"))\n"
        "                   (metrics (analyze-source src))\n"
        "                   (loc (cdr (assq 'loc metrics)))\n"
        "                   (lambdas (cdr (assq 'lambdas metrics))))\n"
        "              (loop (cdr modules)\n"
        "                    (+ total-loc loc)\n"
        "                    (+ total-lambdas lambdas))))))))\n";

    ptr init_str = Sstring(repl_init);
    ptr read_proc = Stop_level_value(Sstring_to_symbol("read"));
    ptr string_port_proc = Stop_level_value(Sstring_to_symbol("open-string-input-port"));
    ptr eval_proc = Stop_level_value(Sstring_to_symbol("eval"));
    ptr interaction_env = Stop_level_value(Sstring_to_symbol("interaction-environment"));

    ptr init_port = Scall1(string_port_proc, init_str);

    // Eval each form in the init string
    fprintf(stderr, "[scheme-bridge] Evaluating init forms...\n");
    int form_count = 0;
    ptr form;
    while (!Seof_objectp(form = Scall1(read_proc, init_port))) {
        ptr env = Scall0(interaction_env);
        Scall2(eval_proc, form, env);
        form_count++;
        fprintf(stderr, "[scheme-bridge]   form %d OK\n", form_count);
    }
    fprintf(stderr, "[scheme-bridge] Init forms done (%d forms)\n", form_count);

    // Set up library path for cyberspace modules
    if (resources_path) {
        fprintf(stderr, "[scheme-bridge] Setting up library paths...\n");
        char lib_setup[4096];
        snprintf(lib_setup, sizeof(lib_setup),
            "(library-directories '((\"%s/lib\" . \"%s/lib\")))",
            resources_path, resources_path);

        ptr setup_str = Sstring(lib_setup);
        ptr read_proc = Stop_level_value(Sstring_to_symbol("read"));
        ptr string_port_proc = Stop_level_value(Sstring_to_symbol("open-string-input-port"));
        ptr eval_proc = Stop_level_value(Sstring_to_symbol("eval"));
        ptr interaction_env = Stop_level_value(Sstring_to_symbol("interaction-environment"));

        ptr setup_port = Scall1(string_port_proc, setup_str);
        ptr form2;
        while (!Seof_objectp(form2 = Scall1(read_proc, setup_port))) {
            ptr env = Scall0(interaction_env);
            Scall2(eval_proc, form2, env);
        }
        fprintf(stderr, "[scheme-bridge] Library dirs set\n");

        // Import modules one at a time
        const char *modules[] = {
            "(import (cyberspace vault))",
            "(import (cyberspace security))",
            "(import (cyberspace server))",
            NULL
        };
        for (int i = 0; modules[i]; i++) {
            fprintf(stderr, "[scheme-bridge] %s\n", modules[i]);
            ptr mod_str = Sstring(modules[i]);
            ptr mod_port = Scall1(string_port_proc, mod_str);
            ptr mod_form = Scall1(read_proc, mod_port);
            ptr env = Scall0(interaction_env);
            Scall2(eval_proc, mod_form, env);
            fprintf(stderr, "[scheme-bridge]   OK\n");
        }
    }

    initialized = true;
    return true;
}

char* scheme_eval(const char *expr) {
    if (!initialized) {
        return strdup("Error: Scheme not initialized");
    }

    // Wrapper with stdout capture and return value
    ptr wrapper = Sstring(
        "(lambda (expr-str) "
        "  (let ([output-port (open-output-string)]) "
        "    (let ([result (parameterize ([current-output-port output-port]) "
        "                    (guard (exn "
        "                            [(and (who-condition? exn) (irritants-condition? exn)) "
        "                             (let ([who (condition-who exn)] "
        "                                   [irr (condition-irritants exn)]) "
        "                               (call-with-string-output-port "
        "                                 (lambda (p) "
        "                                   (display \"Error: \" p) "
        "                                   (when who (display who p) (display \": \" p)) "
        "                                   (display \"variable \" p) "
        "                                   (display (if (pair? irr) (car irr) irr) p) "
        "                                   (display \" is not bound\" p))))] "
        "                            [else "
        "                             (call-with-string-output-port "
        "                               (lambda (p) (display \"Error: evaluation failed\" p)))]) "
        "                      (eval (read (open-string-input-port expr-str)) "
        "                            (interaction-environment))))]) "
        "      (let ([output (get-output-string output-port)]) "
        "        (if (string=? output \"\") "
        "            (call-with-string-output-port "
        "              (lambda (p) (write result p))) "
        "            output)))))"
    );

    // Compile the wrapper
    ptr compile_proc = Stop_level_value(Sstring_to_symbol("compile"));
    ptr read_proc = Stop_level_value(Sstring_to_symbol("read"));
    ptr string_port_proc = Stop_level_value(Sstring_to_symbol("open-string-input-port"));

    ptr wrapper_port = Scall1(string_port_proc, wrapper);
    ptr wrapper_sexp = Scall1(read_proc, wrapper_port);
    ptr wrapper_proc = Scall1(compile_proc, wrapper_sexp);

    // Call the wrapper with the expression
    ptr expr_string = Sstring(expr);
    ptr result_string = Scall1(wrapper_proc, expr_string);

    // Extract C string
    iptr len = Sstring_length(result_string);
    char *result_chars = (char*)malloc(len + 1);
    for (iptr i = 0; i < len; i++) {
        result_chars[i] = (char)Sstring_ref(result_string, i);
    }
    result_chars[len] = '\0';

    return result_chars;
}

void scheme_free_result(char *result) {
    if (result) free(result);
}

void scheme_cleanup(void) {
    if (initialized) {
        Sscheme_deinit();
        initialized = false;
    }
}
