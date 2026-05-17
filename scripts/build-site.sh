#!/usr/bin/env bash

set -e -o pipefail

# Build the site with mkdocs.
cd site
uv run mkdocs build

# Emit JSON schemas from the installed nextest binary so they are served at
# https://nexte.st/schemas/<name>.json. The schemas track whichever nextest is
# on $PATH. In CI, this is the latest release.
mkdir -p output/schemas
cargo nextest self schema repo-config --no-pager > output/schemas/repo-config.json
cargo nextest self schema user-config --no-pager > output/schemas/user-config.json
