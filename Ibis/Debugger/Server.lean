import Ibis.Debugger.Protocol
import Ibis.WorldServer
import Std.Async.TCP

namespace Ibis.Debugger
open Std.Async Spatial Topology

private def checked (result : Except String α) : IO α :=
  IO.ofExcept (result.mapError IO.userError)

private def recvExact (sock : TCP.Socket.Client) (count : Nat) : Async ByteArray := do
  let mut bytes := ByteArray.empty
  while bytes.size < count do
    let some part ← sock.recv? (count - bytes.size).toUInt64 | throw (IO.userError "client disconnected")
    if part.isEmpty then throw (IO.userError "client disconnected")
    bytes := bytes ++ part
  return bytes

private def readPacket (sock : TCP.Socket.Client) : Async Packet := do
  let mut header := ByteArray.empty
  for _ in [:5] do
    let b ← recvExact sock 1
    header := header ++ b
    if b[0]! < 128 then break
  let (len, _) ← checked (decodeVarInt header)
  if len == 0 || len > 2 * 1024 * 1024 then throw (IO.userError "invalid packet length")
  let bytes ← recvExact sock len.toNat
  let (id, payload) ← checked (decodeVarInt bytes)
  return ⟨id, payload⟩

private def sendPacket (sock : TCP.Socket.Client) (id : UInt32) (payload : ByteArray) : Async Unit := do
  sock.send (← checked (encodePacket ⟨id, payload⟩))

private def streamChunks (sock : TCP.Socket.Client) (queue : WorldServer.Queue Obj c Val)
    (center : ChunkPos) (loaded : List ChunkPos) : Async (List ChunkPos) := do
  let desired := chunkBuffer center
  for pos in desired do
    if !loaded.contains pos then
      let chunk ← WorldServer.requestChunk queue pos
      sendPacket sock 0x20 (← checked (encodeWorldChunk chunk))
  return desired

private def handleLogin (sock : TCP.Socket.Client) (server : WorldServer.Server Obj c Val)
    (queue : WorldServer.Queue Obj c Val) : Async Unit := do
  let login ← readPacket sock
  if login.id != 0 then throw (IO.userError "expected Login Start")
  let (username, _) ← checked (decodeString login.payload)
  if username.isEmpty || username.size > 64 then throw (IO.userError "invalid username")
  sendPacket sock 2 (⟨Array.replicate 16 0⟩ ++ buildVarInt username.size.toUInt32 ++ username)
  sendPacket sock 0x24 (← checked buildJoinGame)
  sendPacket sock 0x40 ⟨#[0, 0]⟩
  sendPacket sock 0x42 (be 8 64)
  sendPacket sock 0x34 (be 8 0 ++ be 8 (64.0 : Float).toBits.toNat ++ be 8 0 ++ be 8 0 ++ ⟨#[0, 1]⟩)
  let confirm ← readPacket sock
  let (teleport, _) ← checked (decodeVarInt confirm.payload)
  if confirm.id != 0 || teleport != 1 then throw (IO.userError "expected teleport confirmation")
  let mut center : ChunkPos := ⟨0, 0, 0⟩
  let mut loaded ← streamChunks sock queue center []
  repeat
    let packet ← readPacket sock
    if packet.id == 0x11 || packet.id == 0x12 then
      let next ← checked (parsePosition packet.payload)
      if next != center then
        center := next
        WorldServer.setCursor server next
        sendPacket sock 0x40 (buildVarInt next.x ++ buildVarInt next.z)
        loaded ← streamChunks sock queue next loaded

private def handleConnection (sock : TCP.Socket.Client) (server : WorldServer.Server Obj c Val)
    (queue : WorldServer.Queue Obj c Val) : Async Unit := do
  try
    let handshake ← readPacket sock
    if handshake.id != 0 then throw (IO.userError "expected handshake")
    let (version, state) ← checked (parseHandshake handshake.payload)
    if state == 1 then
      let request ← readPacket sock
      if request.id != 0 then throw (IO.userError "expected status request")
      sendPacket sock 0 (mcString "{\"version\":{\"name\":\"Ibis 1.16.5\",\"protocol\":754},\"players\":{\"max\":1,\"online\":1},\"description\":{\"text\":\"Ibis Compiler Topos Debugger\"}}")
      let ping ← readPacket sock
      if ping.id == 1 && ping.payload.size == 8 then sendPacket sock 1 ping.payload
    else if state == 2 then
      if version != 754 then throw (IO.userError "debugger requires Minecraft 1.16.5 (protocol 754)")
      handleLogin sock server queue
  catch e =>
    IO.eprintln s!"[Ibis Debugger] {e}"
  finally
    try sock.shutdown catch _ => pure ()

/-- Starts the prototype debugger, preserving the existing interpreter CLI. -/
def startDebugger (port : UInt16 := 25545) : IO Unit := do
  let site : GrothendieckSite Unit := ⟨⟨fun _ => true⟩⟩
  let server ← WorldServer.initServer site (.base (u := ()) "Ibis.AST.CoAST.RootSection")
    [⟨(), .id⟩] maximalSieve
  let queue ← Std.CloseableChannel.new
  let worker ← IO.asTask (WorldServer.runServer server queue) (prio := .dedicated)
  try
    let listener ← TCP.Socket.Server.mk
    listener.bind (.v4 ⟨Std.Net.IPv4Addr.ofParts 0 0 0 0, port⟩)
    listener.listen 10
    IO.println s!"[Ibis Debugger] Minecraft 1.16.5 (protocol 754), port {port}"
    (do
      repeat
        let client ← listener.accept
        background (handleConnection client server queue) : Async Unit).block
  finally
    queue.close
    discard <| IO.ofExcept worker.get

end Ibis.Debugger
