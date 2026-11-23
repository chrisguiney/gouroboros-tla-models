# Installing TLA+

## The short version

```sh
make install
make hello
```

If the last line of `make hello` is `Finished in ...` and you saw
`Model checking completed. No error has been found.` above it, you are done.
Go to [Your first model](02-first-model.md).

## What just happened

TLA+ is a language. The tools that read it are Java programs, shipped as one
file called `tla2tools.jar`. So installing TLA+ means two things:

1. **Java.** If `java` on your PATH is version 11 or newer, `make install`
   uses it. Otherwise it downloads Eclipse Temurin 21, a free build of Java,
   into `.tools/jdk/`, without touching any Java you already have.
   To use your system's Java instead, install it first, for example
   `sudo apt install default-jdk` on Debian or Ubuntu (`default-jre` is
   enough). If `.tools/jdk/` already exists, delete it and the tools will use
   the system Java.
2. **The TLA+ tools.** It downloads `tla2tools.jar` (version 1.7.4, the
   latest stable release) into `.tools/`.

Both downloads are checked against a SHA-256 checksum written in
`scripts/install-tla.sh`, so everyone on the team gets byte-identical tools.
If a checksum does not match, the installer stops and deletes the file.

Nothing is installed outside this repository and no `sudo` is needed. To
uninstall, delete `.tools/`.

## The tools inside the jar

You will run these through small wrapper scripts in `bin/`, which find the
right Java for you.

| Command | What it does | Go equivalent |
| --- | --- | --- |
| `bin/sany Spec.tla` | Parses a model and reports syntax or naming errors. | `go vet` |
| `bin/tlc -config Spec.cfg Spec.tla` | Model-checks: explores every reachable state and checks your rules in each one. | `go test`, but exhaustive |

TLC must be run from the directory that contains the `.tla` file, because it
looks for imported modules next to it. The `make` targets do that for you.

## Editor setup (recommended)

TLA+ is much easier to read with syntax highlighting.

- **VS Code** (or VSCodium, Cursor): install the extension
  **TLA+ (Temporal Logic of Actions)**, publisher `tlaplus`, ID
  `tlaplus.vscode-ide`. It highlights syntax, shows parse errors as you type,
  and can run TLC from the command palette. It brings its own copy of the
  tools, so it works even without `make install`, but use `make` in the
  terminal so you get the same versions as everyone else.
- **Vim/Neovim**: search for a `tla` syntax plugin; highlighting is all you need.
- **TLA+ Toolbox**: the older standalone IDE. It still works, but VS Code is
  where current development happens. You do not need it.

### Typing the symbols

TLA+ is written in plain ASCII. The pretty symbols you see in papers are
how the same text is typeset:

| You type | Papers show | Means |
| --- | --- | --- |
| `/\` | ∧ | and |
| `\/` | ∨ | or |
| `~` | ¬ | not |
| `=>` | ⇒ | implies |
| `<=>` | ⇔ | if and only if |
| `\in` | ∈ | is a member of |
| `#` or `/=` | ≠ | not equal |
| `==` | ≜ | "is defined as" |

## Troubleshooting

**`TLA+ is not installed yet. Run: make install`**
You ran a `bin/` command before installing. Run `make install`.

**`No pinned Java for Darwin-arm64` (or another platform)**
The installer only pins a Java download for Linux x86-64 so far. Install Java
11 or newer yourself (macOS: `brew install --cask temurin`), make sure `java -version`
works, and re-run `make install`. It will use your Java and still download the
TLA+ tools.

**`checksum mismatch`**
The download was corrupted or the file on the server changed. Re-run
`make install`. If it fails again, do not edit the checksum to make it pass;
ask in the team channel.

**`Error: Parsing or semantic analysis failed.`**
That is TLA+ syntax, not your install. Run `bin/sany YourSpec.tla` from the
spec's directory to see the error with a line number.

**TLC runs out of memory or seems to hang**
Your model has more states than you expected. Lower the constants (like
`MaxPings` in the hello model) first. A model only needs to be big enough to
show the bug.

## Upgrading

Edit the version, URL, and checksum together in `scripts/install-tla.sh`,
delete `.tools/`, and run `make install`. Get the checksum with
`sha256sum` on a file you downloaded yourself.
