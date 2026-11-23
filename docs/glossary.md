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

**Distinct states**
: How many different states TLC found. A measure of model size, and of how
  many situations a test suite should think about.

**Fairness**
: An assumption that a step which keeps being possible eventually happens.
  Needed for liveness checks. You will not need it for a while.

**Guard**
: The conditions in an action that mention only current (unprimed)
  variables. The action can only happen when they are true.

**Invariant**
: A rule that must hold in every reachable state. The TLA+ version of an
  assertion that runs after every step of every possible run.

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

**Primed variable (`x'`)**
: The value of `x` in the **next** state. `x' = x + 1` means "after this step,
  x is one bigger".

**Safety**
: A property that something bad **never** happens. Invariants are safety
  properties.

**SANY**
: The TLA+ parser. `bin/sany` checks syntax without running anything.

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
