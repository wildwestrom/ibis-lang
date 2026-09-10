import Ibis.Topology
import Std.Sync.Channel

namespace Ibis.WorldServer
open Spatial Topology

structure State (Obj : Type) (c : Obj) (Val : Type) where
  world : World Obj c Val
  cursor : ChunkPos := ⟨0, 0, 0⟩

structure Server (Obj : Type) (c : Obj) (Val : Type) where
  state : Std.Mutex (State Obj c Val)
  generator : ChunkPos → Except String (WorldChunk Obj c Val)

def initServer (site : GrothendieckSite Obj) (payload : Section Val c)
    (arrows : List (CoveringArrow Obj c)) (sieve : Sieve Obj c) : IO (Server Obj c Val) := do
  return ⟨← Std.Mutex.new ⟨⟨site, []⟩, ⟨0, 0, 0⟩⟩,
    fun pos => generateChunk site pos payload arrows sieve⟩

def fetchCursor (server : Server Obj c Val) : IO ChunkPos :=
  server.state.atomically do return (← get).cursor

def setCursor (server : Server Obj c Val) (pos : ChunkPos) : IO Unit :=
  server.state.atomically do modify fun s => { s with cursor := pos }

/-- Serialize lookup and generation so concurrent requests share one cached chunk. -/
def fetchChunk (server : Server Obj c Val) (pos : ChunkPos) : IO (Except String (WorldChunk Obj c Val)) :=
  server.state.atomically do
    let s ← get
    if let some chunk := chunkAt s.world pos then return .ok chunk
    match server.generator pos with
    | .error e => return .error e
    | .ok chunk =>
      set { s with world.chunks := chunk :: s.world.chunks }
      return .ok chunk

def unloadChunk (server : Server Obj c Val) (pos : ChunkPos) : IO Unit :=
  server.state.atomically do
    modify fun s => { s with world.chunks := s.world.chunks.filter (·.coord != pos) }

inductive Request (Obj : Type) (c : Obj) (Val : Type) where
  | fetchCursor : IO.Promise ChunkPos → Request Obj c Val
  | fetchChunk : ChunkPos → IO.Promise (Except String (WorldChunk Obj c Val)) → Request Obj c Val
  | unloadChunk : ChunkPos → Request Obj c Val

abbrev Queue (Obj : Type) (c : Obj) (Val : Type) := Std.CloseableChannel (Request Obj c Val)

/-- Closing the queue ends the worker after draining queued requests. Errors reach the caller. -/
def runServer (server : Server Obj c Val) (queue : Queue Obj c Val) : IO Unit := do
  repeat
    let some req := (← queue.recv).get | break
    match req with
    | .fetchCursor reply => reply.resolve (← fetchCursor server)
    | .fetchChunk pos reply => reply.resolve (← fetchChunk server pos)
    | .unloadChunk pos => unloadChunk server pos

def requestChunk (queue : Queue Obj c Val) (pos : ChunkPos) : Std.Async.Async (WorldChunk Obj c Val) := do
  let reply ← IO.Promise.new
  let sent ← queue.send (.fetchChunk pos reply)
  match ← Std.Async.Async.ofTask sent with
  | .error e => throw (IO.userError (toString e))
  | .ok () => pure ()
  match ← Std.Async.Async.ofPurePromise (pure reply) with
  | .ok chunk => return chunk
  | .error e => throw (IO.userError e)

end Ibis.WorldServer
