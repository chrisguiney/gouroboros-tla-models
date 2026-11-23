#!/usr/bin/env bash
# Installs a private Java runtime and the TLA+ command-line tools into .tools/
# inside this repository. Nothing is installed system-wide and no sudo is
# needed; delete .tools/ to uninstall.
#
# Every download is pinned to an exact version and SHA-256 checksum so everyone
# runs identical tools. To upgrade, change a version, its URL, and its checksum
# together.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS="$ROOT/.tools"

TLA_VERSION="1.7.4"
TLA_URL="https://github.com/tlaplus/tlaplus/releases/download/v${TLA_VERSION}/tla2tools.jar"
TLA_SHA256="936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"

# Eclipse Temurin JDK 21 (long-term support). TLA+ needs Java 11 or newer.
JDK_VERSION="21.0.13.1+2"
JDK_URL=""
JDK_SHA256=""
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)
    JDK_URL="https://github.com/adoptium/temurin21-binaries/releases/download/jdk-21.0.13.1%2B2/OpenJDK21U-jdk_x64_linux_hotspot_21.0.13.1_2.tar.gz"
    JDK_SHA256="bb8a93f9ae6e7a693b2b721e85dbeff26ae1a77447985a8d7afcdd9c7cf6222e"
    ;;
esac

say() { printf '\033[1;34m==>\033[0m %s\n' "$*"; }
die() { printf '\033[1;31merror:\033[0m %s\n' "$*" >&2; exit 1; }
need() { command -v "$1" >/dev/null 2>&1 || die "'$1' is required but not installed."; }

need curl
need tar
if command -v sha256sum >/dev/null 2>&1; then
  sha256() { sha256sum "$1" | cut -d' ' -f1; }
else
  need shasum
  sha256() { shasum -a 256 "$1" | cut -d' ' -f1; }
fi

# fetch URL SHA256 DEST: download, refuse anything whose checksum differs.
fetch() {
  local tmp="$3.partial" got
  curl -fL --progress-bar -o "$tmp" "$1"
  got="$(sha256 "$tmp")"
  if [[ "$got" != "$2" ]]; then
    rm -f "$tmp"
    die "checksum mismatch for $1 (expected $2, got $got)"
  fi
  mv "$tmp" "$3"
}

# Prints the major version of the java on PATH (e.g. 21), or nothing. Java 8
# reports "1.8", which the >= 11 check below rejects.
system_java_major() {
  command -v java >/dev/null 2>&1 || return 0
  java -XshowSettings:properties -version 2>&1 |
    sed -n 's/.*java\.specification\.version = \([0-9]*\).*/\1/p'
}

mkdir -p "$TOOLS"

SYS_JAVA="$(system_java_major)"
if [[ -x "$TOOLS/jdk/bin/java" ]]; then
  say "Java already installed in .tools/jdk (delete it to use your system Java instead)"
elif [[ -n "$SYS_JAVA" ]] && (( SYS_JAVA >= 11 )); then
  say "Using your system Java $SYS_JAVA ($(command -v java)); skipping the Java download"
elif [[ -n "$JDK_URL" ]]; then
  say "Downloading Java (Temurin $JDK_VERSION, about 200 MB)"
  fetch "$JDK_URL" "$JDK_SHA256" "$TOOLS/jdk.tar.gz"
  rm -rf "$TOOLS/jdk"
  mkdir -p "$TOOLS/jdk"
  tar -xzf "$TOOLS/jdk.tar.gz" -C "$TOOLS/jdk" --strip-components=1
  rm -f "$TOOLS/jdk.tar.gz"
elif command -v java >/dev/null 2>&1; then
  say "No pinned Java for $(uname -s)-$(uname -m); using the java on your PATH"
else
  die "No pinned Java for $(uname -s)-$(uname -m). Install Java 11+ (macOS: 'brew install --cask temurin') and re-run."
fi

if [[ -f "$TOOLS/tla2tools.jar" && "$(sha256 "$TOOLS/tla2tools.jar")" == "$TLA_SHA256" ]]; then
  say "TLA+ tools v$TLA_VERSION already installed"
else
  say "Downloading TLA+ tools v$TLA_VERSION"
  fetch "$TLA_URL" "$TLA_SHA256" "$TOOLS/tla2tools.jar"
fi

say "Installed. Next: make hello"
