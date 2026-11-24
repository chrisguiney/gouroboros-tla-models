# Glossary

Plain-language definitions, with a Go comparison where one helps.

**Action**
: One kind of step the system can take, such as `SendPing`. Written as
  conditions on the current state plus a description of the next state.
  Roughly a function that may or may not be allowed to run right now.

**Agency** (Ouroboros term)
: Which side of a mini-protocol is allowed to send the next message. In each
  state exactly one side has agency, or neither does (the done state).

**Behavior**
: One complete run of the system: a sequence of states from the initial state
  onwards. TLC checks every behavior.

**Config file (`.cfg`)**
: Tells TLC which spec to check, which invariants to test, and what values to
  use for constants.

**Counterexample / error trace**
: The sequence of states TLC prints when a rule breaks. The shortest path to
  the bug. Our raw material for Go tests.

**Deadlock**
: A state where no action is possible but the system has not finished. TLC
  reports it by default.

**Cumulative stake distribution** (Cardano term)
: The stake distribution laid end to end: pools in ID order, each owning an
  interval as wide as its stake. A uniform sample then lands in a pool's
  interval with probability equal to its stake share. See
  [model `consensus-tachys`](../specs/consensus-tachys/README.md).

**Distinct states**
: How many different states TLC found. A measure of model size, and of how
  many situations a test suite should think about.

**`ENABLED A`**
: True when action `A` could happen right now. The keep-alive model uses it
  to say "a timeout fires only when nothing else can happen".

**`[f EXCEPT ![k] = v]`**
: A copy of function `f` with key `k` changed to `v`. Inside, `@` means the
  old value of `f[k]`. Like copying a Go map and setting one key.

**Epoch nonce** (Cardano term)
: The random value every VRF check in an epoch uses. Each block folds its VRF
  output into an evolving nonce; a candidate copy stops following it a window
  of slots before the epoch ends, and the next epoch's nonce is made from that
  candidate. See [model `consensus-nonce`](../specs/consensus-nonce/README.md).

**Fairness**
: An assumption that a step which keeps being possible eventually happens.
  Needed for liveness checks. You will not need it for a while.

**Function (`[x \in S |-> e]`)**
: A mapping from every element of `S` to a value, like a Go map whose keys
  are fixed. `view[r]` looks one up. `[Roles -> States]` is the set of all
  such functions, used in type checks.

**Generation** (gOuroboros)
: A counter the protocol engine bumps on every state change. Comparing the
  generation when a message started arriving with the generation when it is
  admitted tells the engine whether the state moved in between.

**Guard**
: The conditions in an action that mention only current (unprimed)
  variables. The action can only happen when they are true.

**Invariant**
: A rule that must hold in every reachable state. The TLA+ version of an
  assertion that runs after every step of every possible run.

**`CASE`, `CHOOSE`**
: `CASE a -> x [] b -> y` is a switch statement. `CHOOSE t \in S : P(t)`
  picks an element of `S` satisfying `P`; use it only when exactly one does.

**Liveness**
: A property that something good **eventually** happens ("every ping is
  eventually answered"). Contrast with safety. Checked with `PROPERTY` in a
  config file.

**Model checking**
: Automatically exploring every reachable state of a model and checking rules
  in each. What TLC does.

**Module**
: One `.tla` file. Its name must match the file name.

**PlusCal**
: A pseudocode-style language that is translated into TLA+. Some people find
  it friendlier for algorithms. We write plain TLA+ here because protocol
  state machines map onto it directly.

**`PrintT(x)` and `ASSUME`**
: `PrintT` prints `x` and is always true. `ASSUME P` asks TLC to check `P`
  about the constants before doing anything else. Together they print tables
  from a model (`KeepAliveTable.tla`).

**`PROPERTY` (in a `.cfg`)**
: Checks a formula about whole behaviors, such as `[][P]_vars` ("every step
  satisfies `P`"), rather than about single states like `INVARIANT` does.

**Primed variable (`x'`)**
: The value of `x` in the **next** state. `x' = x + 1` means "after this step,
  x is one bigger".

**Public leader schedule** (Ouroboros Tachys)
: A schedule anyone can compute that names exactly one pool for every slot,
  replacing Praos's private VRF lottery. See
  [model `consensus-tachys`](../specs/consensus-tachys/README.md).

**`RECURSIVE F(_)`**
: Declares an operator that calls itself, like a recursive Go function.
  Model `consensus-tachys`'s `Sum` adds up a set this way.

**Record (`[a |-> x, b |-> y]`)**
: A value with named fields, like a Go struct. `m.a` reads a field. The
  keep-alive model's messages are records with `type`, `cookie`, and
  `oversized` fields.

**Safety**
: A property that something bad **never** happens. Invariants are safety
  properties.

**SANY**
: The TLA+ parser. `bin/sany` checks syntax without running anything.

**Sequence (`<<a, b>>`)**
: An ordered list, used for inboxes. `Append(s, x)` adds to the end,
  `Head(s)` is the first element, `Tail(s)` is the rest, `Len(s)` the length,
  `<<>>` the empty one. Also used for tuples. Needs `EXTENDS Sequences`.

**Spec / specification**
: A TLA+ description of a system. Also the name we give the top-level formula,
  `Spec == Init /\ [][Next]_vars`.

**State**
: One value for every variable at one moment.

**State space explosion**
: The number of states grows very fast as constants grow. Keep constants as
  small as still shows the behavior you care about.

**Stuttering**
: A step where nothing changes. TLA+ always allows it; that is what the
  `[...]_vars` in `Spec` means.

**TLC**
: The TLA+ model checker. `bin/tlc`.

**`UNCHANGED x`**
: Shorthand for `x' = x`. Every action must say what happens to every
  variable.
