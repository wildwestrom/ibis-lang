"""Exercise the Lean debugger over TCP; no Minecraft installation required."""
import json
from pathlib import Path
import socket
import struct
import subprocess
import time

root = Path(__file__).resolve().parent.parent


def varint(n):
    n &= 0xffffffff
    out = bytearray()
    while n > 127:
        out.append((n & 127) | 128)
        n >>= 7
    return bytes(out + bytes([n]))


def string(s):
    b = s.encode()
    return varint(len(b)) + b


def exact(sock, n):
    out = b""
    while len(out) < n:
        data = sock.recv(n - len(out))
        assert data, "unexpected disconnect"
        out += data
    return out


def read_varint(sock):
    n = 0
    for i in range(5):
        b = exact(sock, 1)[0]
        n |= (b & 127) << (i * 7)
        if b < 128:
            return n
    raise AssertionError("oversized VarInt")


def send(sock, pid, payload=b"", fragmented=False):
    data = varint(pid) + payload
    data = varint(len(data)) + data
    if fragmented:
        for b in data:
            sock.sendall(bytes([b]))
    else:
        sock.sendall(data)


def packet(sock):
    import io
    data = io.BytesIO(exact(sock, read_varint(sock)))
    class Reader:
        recv = data.read
    pid = read_varint(Reader())
    return pid, data.read()


with socket.socket() as reservation:
    reservation.bind(("127.0.0.1", 0))
    port = reservation.getsockname()[1]
proc = subprocess.Popen([str(root / ".lake/build/bin/ibis"), "debugger", str(port)],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
try:
    def connect(state):
        sock = socket.create_connection(("127.0.0.1", port), timeout=5)
        send(sock, 0, varint(754) + string("localhost") + struct.pack(">H", port) + varint(state), True)
        return sock

    for _ in range(100):
        assert proc.poll() is None, "debugger exited at startup"
        try:
            with connect(1) as sock:
                send(sock, 0)
                pid, data = packet(sock)
                # Status string uses a two-byte length for this fixture.
                assert pid == 0 and json.loads(data[2:])["version"]["protocol"] == 754
                ping = struct.pack(">q", -123456789)
                send(sock, 1, ping)
                assert packet(sock) == (1, ping)
            break
        except ConnectionRefusedError:
            time.sleep(.05)
    else:
        raise AssertionError("debugger never listened")

    def login():
        sock = connect(2)
        send(sock, 0, string("LeanTest"))
        assert packet(sock) == (2, bytes(16) + string("LeanTest"))
        for expected in [0x24, 0x40, 0x42, 0x34]:
            assert packet(sock)[0] == expected
        send(sock, 0, varint(1))
        assert len(chunks(sock, 9)) == 9
        return sock

    def chunks(sock, count):
        positions = set()
        for _ in range(count):
            pid, data = packet(sock)
            assert pid == 0x20
            positions.add(struct.unpack(">ii", data[:8]))
            # Full chunk, section mask, named heightmap, biome VarInts, stone section.
            height = sum(64 << (i * 9) for i in range(7))
            nbt = b'\x0a\x00\x00\x0c\x00\x0fMOTION_BLOCKING' + struct.pack('>i', 36) + struct.pack('>Q', height) * 36 + b'\x00'
            section = struct.pack('>h', 4096) + b'\x04\x01\x01' + varint(256) + bytes(2048)
            expected = data[:8] + b'\x01\x08' + nbt + varint(1024) + bytes([1]) * 1024 + varint(len(section)) + section + b'\x00'
            assert data == expected, "chunk wire layout"
        return positions

    with login() as first, login() as second:
        for sock in [first, second]:
            send(sock, 0x11, struct.pack(">ddd?", 16, 64, 0, True))
            assert packet(sock) == (0x40, varint(1) + varint(0))
            assert chunks(sock, 3) == {(2, z) for z in [-1, 0, 1]}
        send(first, 0x12, struct.pack(">dddff?", -0.5, 64, 0, 0, 0, True))
        assert packet(first) == (0x40, varint(-1) + varint(0))
        assert chunks(first, 6) == {(x, z) for x in [-2, -1] for z in [-1, 0, 1]}
    # Invalid frame must close only its connection; the listener remains usable.
    with socket.create_connection(("127.0.0.1", port), timeout=5) as sock:
        sock.sendall(b'\xff\xff\xff\xff\x7f')
        assert sock.recv(1) == b''
    with connect(1) as sock:
        send(sock, 0)
        assert packet(sock)[0] == 0
    print("Debugger socket checks passed: status/ping, login, chunks, two-client movement, negative coordinates, malformed frame")
finally:
    proc.terminate()
    try:
        proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()
