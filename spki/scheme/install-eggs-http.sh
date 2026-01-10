#!/bin/sh
# Install eggs via HTTP (bypass broken SSL on this machine)
set -e

EGGS="srfi-1 srfi-4 srfi-13 srfi-14 srfi-18 srfi-69"
SERVER="http://chicken.kitten-technologies.co.uk/henrietta.cgi"

for egg in $EGGS; do
    echo "=== Installing $egg ==="
    cd /tmp
    rm -rf "$egg"
    mkdir "$egg"
    cd "$egg"

    # Download and extract
    curl -s "$SERVER?name=$egg&release=5" | perl -ne '
        if (/^#\|--------------------.*?"\.\/([^"]+)"/) {
            close F if $file;
            $file = $1;
            open F, ">", $file or die "Cannot create $file: $!";
        } elsif ($file) {
            print F $_;
        }
    '

    # Install from local directory
    chicken-install -l /tmp/"$egg"
done

echo "Done. Run: cyberspace"
