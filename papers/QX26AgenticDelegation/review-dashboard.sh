#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/../.." && pwd)"
PAPER_DIR="$(basename "$SCRIPT_DIR")"

exec "${ROOT_DIR}/scripts/launch_review_dashboard.sh" --paper "$PAPER_DIR" "$@"
