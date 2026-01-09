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

Before publishing RFCs, always:

1. Generate all formats (only rebuilds stale/missing files):

       cd spki/scheme/docs/rfc && ./generate-rfcs.sh

2. Rsync to yoyodyne:

       rsync -avz --delete spki/scheme/docs/rfc/ www.yoyodyne.com:/www/yoyodyne/ddp/cyberspace/

3. Fix permissions (rsync preserves local non-world-readable permissions):

       ssh www.yoyodyne.com 'chmod 755 /www/yoyodyne/ddp/cyberspace && chmod 644 /www/yoyodyne/ddp/cyberspace/*'
