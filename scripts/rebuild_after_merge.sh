#!/bin/bash

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COQ_DIR="$ROOT/coq"
EXTRACT_DIR="$ROOT/extract_coq"
EXTRACT_ML_DIR="$EXTRACT_DIR/ml"
MLQBLUE_DIR="$ROOT/mlqblue"
QBLUELIB_DIR="$MLQBLUE_DIR/qbluelib"
OPAMROOT="$HOME/.opam"
QBLUE_OPAM_SWITCH="${QBLUE_OPAM_SWITCH:-${OPAMSWITCH:-qblue-coq816}}"

QBLUE_OPAM_SWITCH="qblue-coq816"
QBLUE_PYTHON_MODULE="python/3.11.13"

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

python_bin() {
  printf '%s\n' "python3"
}

require_python37() {
  "$(python_bin)" -c 'import sys; raise SystemExit(0 if sys.version_info >= (3, 7) else 1)' || die \
    "python 3.7+ is required for extract_coq/src/prune.py
The script loads $QBLUE_PYTHON_MODULE and expects python3 to come from that module."
}

ensure_module_cmd() {
  if type module >/dev/null 2>&1; then
    return 0
  fi

  local init
  for init in /usr/share/lmod/lmod/init/bash /etc/profile.d/modules.sh /usr/share/Modules/init/bash; do
    if [[ -f "$init" ]]; then
      # shellcheck disable=SC1090
      source "$init"
      break
    fi
  done

  type module >/dev/null 2>&1
}

maybe_load_python_module() {
  ensure_module_cmd || die \
    "the environment-modules command is unavailable"

  log "Loading python module: $QBLUE_PYTHON_MODULE"
  module load "$QBLUE_PYTHON_MODULE"
}

clean_generated_artifacts() {
  log "Cleaning stale Coq and extraction artifacts"
  find "$COQ_DIR" -mindepth 1 -maxdepth 1 \( -name '*.vo' -o -name '*.glob' -o -name '*.vos' -o -name '*.vok' \) -delete
  rm -rf "$COQ_DIR/.coq-native"

  find "$EXTRACT_DIR/src" -mindepth 1 -maxdepth 2 \( -name '*.vo' -o -name '*.glob' -o -name '*.vos' -o -name '*.vok' \) -delete
  rm -rf "$EXTRACT_DIR/src/.coq-native" "$EXTRACT_DIR/src/extracted" "$EXTRACT_ML_DIR"
}

require_cmd opam
require_cmd make
require_cmd cp

require_file "$COQ_DIR/_CoqProject"
require_file "$EXTRACT_DIR/extract.sh"
require_file "$MLQBLUE_DIR/dune-project"

log "Repo root: $ROOT"
log "Using opam switch: $QBLUE_OPAM_SWITCH"
maybe_load_python_module
require_cmd "$(python_bin)"
log "Using python: $(python_bin)"
eval "$(opam env --switch="$QBLUE_OPAM_SWITCH")"

require_opam_package coq
require_opam_package coq-quantumlib
require_opam_package coq-sqir
require_opam_package coq-voqc
require_python37

require_cmd coq_makefile
log "Regenerating coq/Makefile"
(
  cd "$COQ_DIR"
  coq_makefile -f _CoqProject -o Makefile
)

clean_generated_artifacts

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
