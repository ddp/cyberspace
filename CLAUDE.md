# Claude Code Project Configuration

## Commit Attribution

RFC-040 is authoritative for AI co-authorship for the entire project.

All commits credit only the human author:

    Author: Derrell Piper <ddp@eludom.net>

Do not add co-author lines, robot emoji, or Claude Code attribution to
individual commits. The project-level RFC handles this once and for all.

## Design Philosophy

- Newton: The data model (soup, objects, queries)
- Stephenson: The prose (engineering-grounded, mathematically honest)
- Not Gibson: No style over substance

## Scope

Single-realm model. Enclaves with own consensus policies are explicitly
deferred as a very hard problem space.

## Publishing to Yoyodyne

Generate and publish RFCs (handles stale detection, format generation, rsync, permissions):

    cd spki/scheme/docs/rfc && ./generate-rfcs.sh

Published to: https://www.yoyodyne.com/ddp/cyberspace/
