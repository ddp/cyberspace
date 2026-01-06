# Installing Coq for SPKI TCB Verification

## Quick Start (macOS)

```bash
# Install Coq via Homebrew
brew install coq

# Verify installation
coqc --version

# Build SPKI proofs
cd /Users/ddp/cyberspace/spki/coq
make

# Check status
make status
```

## Alternative: Install via opam

```bash
# Install opam (OCaml package manager) if not already installed
brew install opam

# Initialize opam
opam init -y
eval $(opam env)

# Install Coq
opam install coq

# Verify
coqc --version
```

## Expected Output

After installation, `coqc --version` should show:
```
The Coq Proof Assistant, version 8.18.0
compiled with OCaml 5.1.0
```

(Version may vary, 8.15+ required)

## Building the Proofs

```bash
cd /Users/ddp/cyberspace/spki/coq

# Build all proofs
make

# Expected output:
# COQC Signature.v
# Signature.vo compiled successfully
```

## Verification Without Installation

If you don't want to install Coq locally, you can:

1. **Read the proofs**: All `.v` files are human-readable
2. **Use online Coq**: https://coq.vercel.app/
   - Upload `Signature.v`
   - Interactively step through proofs
3. **Docker**: Run Coq in a container
   ```bash
   docker run -v $(pwd):/work -w /work coqorg/coq:latest make
   ```

## Next Steps

After installation:

```bash
# Build and check proofs
make check

# View proof status
make status

# Generate HTML documentation
make html
open html/toc.html
```

## Troubleshooting

### Error: "coq_makefile: command not found"

Solution: Make sure Coq binaries are in your PATH:
```bash
# Add to ~/.zshrc
export PATH="/opt/homebrew/bin:$PATH"
source ~/.zshrc
```

### Error: "Cannot find library Coq.Lists.List"

Solution: Coq's standard library should be installed automatically. Reinstall:
```bash
brew reinstall coq
```

### Build fails with "Module not found"

Check your `_CoqProject` file lists all dependencies correctly.

## IDE Support

### CoqIDE (GUI)

```bash
brew install coqide
coqide Signature.v &
```

### Emacs + Proof General

```bash
# Install Proof General
opam install coq-lsp

# Add to ~/.emacs
(require 'proof-general)
(setq coq-prog-name "coqtop")
```

### VSCode + VSCoq

Install the VSCoq extension from the marketplace.

## Resources

- Coq documentation: https://coq.inria.fr/documentation
- Software Foundations: https://softwarefoundations.cis.upenn.edu/
- Coq'Art (book): "Interactive Theorem Proving and Program Development"
