#!/bin/bash

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COQ_DIR="$ROOT/coq"
EXTRACT_DIR="$ROOT/extract_coq"
EXTRACT_ML_DIR="$EXTRACT_DIR/ml"
MLQBLUE_DIR="$ROOT/mlqblue"
QBLUELIB_DIR="$MLQBLUE_DIR/qbluelib"

QBLUE_OPAM_SWITCH="${QBLUE_OPAM_SWITCH:-${OPAMSWITCH:-qblue}}"

log() {
  printf '[rebuild_after_merge] %s\n' "$*"
}

die() {
  printf '[rebuild_after_merge] ERROR: %s\n' "$*" >&2
  exit 1
}

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || die "missing required command: $1"
}

require_file() {
  [[ -f "$1" ]] || die "missing required file: $1"
}

require_opam_package() {
  local pkg="$1"
  opam list --installed --short | grep -Fxq "$pkg" || die \
    "missing opam package in switch $QBLUE_OPAM_SWITCH: $pkg
Install the Coq dependencies from coq/opam-switch.export or at least:
  coq
  coq-quantumlib
  coq-sqir
  coq-voqc"
}

require_cmd opam
require_cmd python3
require_cmd make
require_cmd cp

require_file "$COQ_DIR/_CoqProject"
require_file "$EXTRACT_DIR/extract.sh"
require_file "$MLQBLUE_DIR/dune-project"

log "Repo root: $ROOT"
log "Using opam switch: $QBLUE_OPAM_SWITCH"
eval "$(opam env --switch="$QBLUE_OPAM_SWITCH")"

require_opam_package coq
require_opam_package coq-quantumlib
require_opam_package coq-sqir
require_opam_package coq-voqc

if [[ ! -f "$COQ_DIR/Makefile" ]]; then
  require_cmd coq_makefile
  log "Generating coq/Makefile"
  (
    cd "$COQ_DIR"
    coq_makefile -f _CoqProject -o Makefile
  )
fi

log "Building Coq sources"
(
  cd "$COQ_DIR"
  make
)

log "Running extraction"
(
  cd "$EXTRACT_DIR"
  bash extract.sh
)

require_file "$EXTRACT_ML_DIR/QBlueCompile.ml"
require_file "$EXTRACT_ML_DIR/QBlueSynth.ml"
require_file "$EXTRACT_ML_DIR/bridge.ml"
require_file "$EXTRACT_ML_DIR/api.py"
require_file "$EXTRACT_ML_DIR/networks.py"

log "Refreshing mlqblue/qbluelib"
mkdir -p "$QBLUELIB_DIR"
find "$QBLUELIB_DIR" -mindepth 1 -maxdepth 1 \( -name '*.ml' -o -name '*.py' \) -delete

shopt -s nullglob
extracted_files=( "$EXTRACT_ML_DIR"/*.ml "$EXTRACT_ML_DIR"/*.py )
shopt -u nullglob

(( ${#extracted_files[@]} > 0 )) || die "extract_coq/ml did not produce any .ml or .py files"
cp "${extracted_files[@]}" "$QBLUELIB_DIR"/

log "Building mlqblue"
(
  cd "$MLQBLUE_DIR"
  dune build
)

require_file "$MLQBLUE_DIR/_build/default/performance.exe"

log "Done. Built $MLQBLUE_DIR/_build/default/performance.exe"
