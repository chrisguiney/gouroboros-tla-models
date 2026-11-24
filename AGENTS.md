# Agent instructions

This repository holds TLA+ models of gouroboros mini-protocols. Its audience
is engineers who are new to TLA+, so readability beats cleverness.

- Install tools with `make install`; never install Java or TLA+ system-wide.
- Run `make check` before committing a model. It checks every `.cfg` under
  `specs/` except `*Bug.cfg`, which are intentionally failing teaching
  examples.
- One directory per model under `specs/`, numbered in learning order.
- Comment every new TLA+ construct the first time a model uses it, and link
  the doc that explains it. Add new terms to `docs/glossary.md`.
- Write every definition for a reader who does not know TLA+: an
  `In English:` comment above it reading the whole definition as a sentence,
  and a trailing comment on each clause that changes a variable or sets a
  condition. Start each module with a "how to read the symbols" legend, or
  point to one.
- Cite a source for every rule in a model, before writing it: the network
  specification or reference implementation in IntersectMBO/ouroboros-network,
  pinned to a commit, with file, section, and line numbers. List sources in
  the model's README and tag rules in the `.tla` (`[S1]`). A rule with no
  source is marked UNSOURCED with the reason. Never model from memory alone.
- Name the gouroboros file a model is based on (for example
  `protocol/keepalive/keepalive.go`) in the module header comment.
- A counterexample that reflects a real gouroboros behavior becomes a Go test
  in gouroboros, through that repository's normal issue and pull-request
  process. This repository does not hold Go code.
- Conventional Commits with DCO sign-off (`git commit -s`).
