#!/bin/bash
# Test script for Cyberspace API
# Tests basic endpoints and functionality

set -e

API_URL="http://localhost:8080"
TOKEN=""

echo "═══════════════════════════════════════════════════════"
echo "Cyberspace API Test Suite"
echo "═══════════════════════════════════════════════════════"
echo ""

# Function to test endpoint
test_endpoint() {
    local method="$1"
    local path="$2"
    local data="$3"
    local desc="$4"

    echo "Testing: $desc"
    echo "  $method $path"

    if [ -n "$data" ]; then
        curl -s -X "$method" \
             -H "Content-Type: application/json" \
             -H "Authorization: Capability $TOKEN" \
             -d "$data" \
             "$API_URL$path" | python3 -m json.tool
    else
        curl -s -X "$method" \
             -H "Authorization: Capability $TOKEN" \
             "$API_URL$path" | python3 -m json.tool
    fi

    echo ""
    echo "---"
    echo ""
}

# 1. Health Check
echo "1. Health Check"
test_endpoint "GET" "/health" "" "Server health status"

# 2. Authentication
echo "2. Authentication"
test_endpoint "POST" "/auth/login" '{"username":"alice","password":"secret"}' "Login and get capability token"

# TODO: Extract token from response
# TOKEN="..."

# 3. Library Search
echo "3. Library Search"
test_endpoint "GET" "/library/search?q=lamport" "" "Search for 'lamport' in library"

# 4. Library Catalog
echo "4. Library Catalog"
test_endpoint "GET" "/library/catalog" "" "Get full library catalog"

# 5. Crypto - Lamport Keygen
echo "5. Crypto - Lamport Keygen"
test_endpoint "POST" "/crypto/lamport/keygen" '{"bits":256}' "Generate Lamport keypair"

# 6. Implementation List
echo "6. Implementation List"
test_endpoint "GET" "/impl/list" "" "List all implementations"

echo "═══════════════════════════════════════════════════════"
echo "Test suite complete"
echo "═══════════════════════════════════════════════════════"
