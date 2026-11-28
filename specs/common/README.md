# shared modules

Modules other models `EXTEND` or `INSTANCE`. They hold no configs of their
own; `bin/_java` puts this directory on TLC's library path, so any spec can
name them.

| Module | What it is | Used by |
| --- | --- | --- |
| `GoConcurrency.tla` | Go's primitives as values a spec keeps in its own variables: a channel with a capacity (blocking send and receive, close, a send on a closed channel or a second close as a reachable panic state), a close-only signal channel, a broadcast generation, `select`'s default case, `sync.Mutex`, `sync.RWMutex` with writer preference, `sync.WaitGroup`, `sync.Once` and `time.Timer` | `connection/ConnectionEngines.tla`, `common/Engine.tla` |
| `Engine.tla` | one `protocol.Protocol` as a connection sees it (gOuroboros `0c00b799`): `started`, `stopChan`, the send queue, a running handler, `DoneChan`, the join, the muxer registration and the muxer's done, with one rule per object that every engine step obeys. `DoneAfterJoin` is the contract that a completed join implies `DoneChan` is closed | refined by `engine/EngineLifecycleRefinement.tla` and by each engine of `connection/ConnectionEngines.tla` (`EnginesRefine`) |

Each goroutine stays a process of the spec that uses `GoConcurrency`: the
module only says when a step on a primitive is enabled and what it leaves
behind. Results of the refinement checks are in
[the engine README](../engine/README.md) (slice 4, fourth pass) and
[the connection README](../connection/README.md) (part 8).
