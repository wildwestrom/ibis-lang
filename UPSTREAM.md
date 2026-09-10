# Haskell upstream

The Lean implementation follows the behavior of
[megabytesofrem/ibis-lang](https://github.com/megabytesofrem/ibis-lang).

## Baseline

- Reference commit: `b721f1ad046102e3864add68a7582e1c9416c281`
- Commit subject: `server: Fixed vertical chunk generation in debugger`
- Last checked against `upstream/main`: 2026-09-10
- The Haskell files in `src/` match this commit.

This identifies the source used for the port, not a claim of complete behavioral
equivalence. Corrections and unfinished features are documented in
[LEAN_PORT.md](LEAN_PORT.md). The parity tests cover shared working evaluator cases
and chunk/NBT wire-format fixtures.

## Remotes

- `upstream`: `https://github.com/megabytesofrem/ibis-lang.git`, the original
  Haskell project.
- `origin`: `git@github.com:wildwestrom/ibis-lang.git`, the user's fork and the
  home of this Lean port. Push completed Lean port commits here.

This fork tracks the Haskell project's development by porting each upstream
change into Lean as it arrives. Keep these repository names and remotes;
there is no planned move to a separate `ibis-lean` repository. The retained
Haskell snapshot serves as a reference for translation and parity tests.

## Following changes with Jujutsu

```sh
jj git fetch --remote upstream
jj log -r 'b721f1ad046102e3864add68a7582e1c9416c281..main@upstream'
```

Keep `main@upstream` untracked in Jujutsu so fetching Haskell changes does not
automatically move or merge into the local Lean `main` bookmark. The remote
bookmark remains available for inspection after fetching.

Review each upstream change, translate relevant behavior, and add regression or
parity tests. Update the pinned Haskell reference and this baseline together
after running `lake build`, `lake exe ibisTests`, and
`python3 test/lean-parity.py`, and `python3 test/debugger-socket.py`. Record any deferred changes explicitly; fetching
alone does not advance the port's baseline. Upstream commits should not be
automatically merged into the Lean implementation.

## Ported through `b721f1a`

Ported `fe7c166` (protocol cleanup, chat, keepalives) and `b721f1a` (vertical
sections). The Haskell source, executable entry point, and Cabal file match this
baseline. Lean already separated protocol encoding from server coordination;
it now decodes typed play events, echoes chat as escaped JSON system messages,
and sends an increasing 64-bit keepalive every fifteen seconds after login.
The keepalive timer is cancelled when the connection's play session ends.
Join Game now advertises one player and reduced debug information.

WorldServer requests cover a 3×3 horizontal view and the center Y section plus
its neighbors, limited to sections 0–15. Login starts with center section 3.
The encoder uses the section's bitmask and heightmap rather than a fixed Y=0
coordinate and Y=64 surface. Like upstream, only the center section is rendered
per X/Z column; combining multiple sections into one column remains unfinished.

Additional intentional corrections:

- Vertical movement resends the new center section even when it was already
  prefetched. Upstream only sends entering sections, which can leave the visible
  column unchanged after moving vertically.
- Movement outside the vertical world bounds clamps the view center to 0–15
  rather than wrapping negative Y to Word32 and producing an empty view.
- Malformed or unsupported play packets remain ignorable. Position-and-look
  packets require both angles and the on-ground field; invalid UTF-8 chat and
  non-finite movement are ignored.
- JSON escaping uses Lean's existing JSON printer. Packet writes submit complete
  frames through the standard library's TCP queue, including keepalive writes.

Validation: `lake build`, `lake exe ibisTests` (23 groups),
`python3 test/lean-parity.py` (19 comparisons), and
`python3 test/debugger-socket.py` (including vertical-only movement, bedrock and
ceiling limits, chat escaping, and keepalive delivery during a partial inbound
frame) passed. No real Minecraft client or Haskell network executable was tested.

## Previously ported through `30a47127`

Fetched and reviewed `19b7dac` (WorldServer polling) and `30a4712` (debugger).
The Haskell `src/`, `app/Main.hs`, Cabal configuration, and semantics TeX source
are refreshed. Generated paper build artifacts are intentionally not refreshed.

Lean adds `Ibis/WorldServer.lean` and `Ibis/Debugger/{NBT,Protocol,Server}.lean`.
`lake exe ibis debugger [PORT]` starts the WorldServer worker and TCP debugger
(default 25545), using only Lean's standard library. The existing interpreter
commands remain available. Status/ping, offline login, dimension/biome NBT,
initial nine-chunk view, movement-driven streaming, and negative coordinates
follow upstream's Minecraft 1.16.5 / protocol 754 implementation. Upstream's
startup banner incorrectly names 1.20.1; Lean advertises 1.16.5.

Intentional corrections:

- Generated chunks are cached atomically; upstream returns them without insertion.
  FetchCursor reads the stored cursor instead of returning the origin.
- A closeable FIFO channel and promises replace STM. Generation errors reach the
  requester, and closing the queue drains pending requests and stops the worker.
- View centers are per connection, so one client's movement cannot suppress
  another client's chunk stream. The shared cursor records the latest movement.
- Status waits for the status request before replying, so ping echoes correctly.
  Login checks protocol version and teleport confirmation.
- Frame sizes, VarInt overflow, truncated fields, non-finite/out-of-range movement,
  NBT lengths, and homogeneous NBT lists are checked. Unsupported chunk heights
  return errors rather than panicking.
- Lean retains the older `Region`, `CoChunk`, and `CoWorld` records as compatibility
  types after upstream removed them; the debugger uses `WorldChunk`.

At this baseline, chunks rendered a fixed stone platform, not section values;
authentication, keepalives, automatic cache eviction, block editing, and a full
Minecraft server implementation were absent. Keepalives are now ported above. A real
Minecraft client session has not been tested. The Haskell network executable
was not built (the installed GHC environment lacks `network`).

Validation: `lake build`, `lake exe ibisTests` (22 groups),
`python3 test/lean-parity.py` (13 evaluator, 3 chunk, and 3 NBT comparisons), and
`python3 test/debugger-socket.py` (real TCP status/ping, login, exact chunk bytes,
two-client movement, negative coordinates, malformed frames).

## Previously ported through `4b5194ac`

The Haskell snapshot, Cabal configuration, and `example/vect.ibis` match the
reference. Lean now supports the chunk wire record, empty sections,
position-bearing inclusions, world/region records, chunk lookup, local section
restriction, and initial world generation. `LocalCoord` and `VoxelChunk` remain
aliases for the renamed Lean types. Chunk generation now takes `Spatial.ChunkPos`
(unsigned 32-bit coordinates), following upstream.

Intentional differences:

- Zero in any world dimension produces no chunks instead of unsigned underflow.
- Invalid covers return `Except.error` rather than throwing a runtime exception.
- Arrow path comparison does not imply object equality. `eqArrow` checks target
  equality using `DecidableEq`; it does not reproduce upstream's `unsafeCoerce`.
  `localComposition` takes the intermediate object explicitly.
- Serialization rejects lengths that do not fit the 32-bit format. Decoding
  validates lengths against available bytes before allocating; trailing bytes
  are ignored, matching upstream. The signed wire coordinates are separate from
  unsigned spatial coordinates; no automatic conversion is introduced.

At this earlier baseline, the WorldServer scaffold was deferred; it is now ported
as described above. The aspirational list/site syntax added to `vect.ibis` remains deferred. Serialization
stores opaque arrow IDs and section bytes; connecting them to live world data
is not implemented upstream or in Lean.

Validation: `lake build`, `lake exe ibisTests` (20 groups), and
`python3 test/lean-parity.py` (13 evaluator and 3 chunk-format comparisons) passed.
