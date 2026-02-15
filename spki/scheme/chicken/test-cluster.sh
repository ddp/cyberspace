#!/bin/bash
# Test cluster connectivity between two nodes
# Run in two terminals:
#   Terminal 1: ./test-cluster.sh alpha 4433
#   Terminal 2: ./test-cluster.sh beta 4434 localhost 4433

NODE_NAME=${1:-alpha}
NODE_PORT=${2:-4433}
CONNECT_HOST=${3:-}
CONNECT_PORT=${4:-}

echo "Starting node: $NODE_NAME on port $NODE_PORT"

if [ -n "$CONNECT_HOST" ]; then
  echo "Will connect to: $CONNECT_HOST:$CONNECT_PORT"
  ./repl <<EOF
(node-listen $NODE_PORT "$NODE_NAME")
(node-connect "$CONNECT_HOST" $CONNECT_PORT)
(nodes)
(banner)
EOF
else
  echo "Waiting for connections..."
  ./repl <<EOF
(node-listen $NODE_PORT "$NODE_NAME")
(node-accept)
(nodes)
(banner)
EOF
fi
