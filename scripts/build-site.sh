#!/usr/bin/env bash

set -e -o pipefail

# Build the site with mkdocs.
cd site
uv run mkdocs build

# Emit the repository config JSON schema from the installed nextest binary so
# it is served at https://nexte.st/schemas/repo-config.json. The schema tracks
# whichever nextest is on $PATH. In CI, this is the latest release.
mkdir -p output/schemas
cargo nextest self schema repo-config --no-pager > output/schemas/repo-config.json
