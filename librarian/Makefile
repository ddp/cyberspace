# Cyberspace Librarian - Build System

LIBRARY_ROOT = $(HOME)/cyberspace/library
INDEX_DB = library-index.db
INDEX_TEXT = library-index.txt

.PHONY: all index clean test

all: index

# Build the searchable index
index: $(INDEX_TEXT)
	@echo "Index built: $(INDEX_TEXT)"
	@wc -l $(INDEX_TEXT)

$(INDEX_TEXT): index-builder.scm
	./index-builder.scm $(LIBRARY_ROOT) > $(INDEX_TEXT) 2>&1

# Clean generated files
clean:
	rm -f $(INDEX_TEXT) $(INDEX_DB)

# Quick test
test:
	./index-builder.scm $(LIBRARY_ROOT) 2>&1 | head -50

# Show summary
summary: $(INDEX_TEXT)
	@echo "=== Library of Cyberspace Summary ==="
	@grep "Total collections:" $(INDEX_TEXT)
	@grep "Found.*INDEX.md" $(INDEX_TEXT)
	@echo ""
	@echo "Recent additions:"
	@tail -20 $(INDEX_TEXT)

.DEFAULT_GOAL := all
