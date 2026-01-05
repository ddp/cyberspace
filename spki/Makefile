.PHONY: build test install clean

build:
	@echo "Building SPKI tools..."
	@if command -v dune > /dev/null 2>&1; then \
		dune build; \
	else \
		echo "Error: dune not found. Please run: opam init && opam install dune"; \
		exit 1; \
	fi

test: build
	@echo "Running tests..."
	@dune runtest

install: build
	@echo "Installing SPKI tools to ~/bin..."
	@mkdir -p ~/bin
	@cp _build/default/bin/spki_keygen.exe ~/bin/spki-keygen
	@cp _build/default/bin/spki_cert.exe ~/bin/spki-cert
	@cp _build/default/bin/spki_verify.exe ~/bin/spki-verify
	@cp _build/default/bin/spki_show.exe ~/bin/spki-show
	@chmod +x ~/bin/spki-*
	@echo "✓ Installed to ~/bin/"
	@echo "  spki-keygen  - Generate keypair"
	@echo "  spki-cert    - Create and sign certificate"
	@echo "  spki-verify  - Verify certificate chain"
	@echo "  spki-show    - Display certificate"

clean:
	@dune clean

help:
	@echo "SPKI Build Commands:"
	@echo "  make build    - Build all tools"
	@echo "  make test     - Run test suite"
	@echo "  make install  - Install tools to ~/bin"
	@echo "  make clean    - Clean build artifacts"
