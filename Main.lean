import Ibis

open Ibis

private def usage : String :=
  "Usage: ibis parse FILE | elab FILE | check FILE | eval EXPR | type EXPR | debugger [PORT]\n" ++
  "  parse  print the surface AST\n" ++
  "  elab   elaborate declarations to core syntax (does not type-check)\n" ++
  "  check  type-check supported definitions\n" ++
  "  eval   normalize a closed expression\n" ++
  "  type   infer a closed expression's type"

def main (args : List String) : IO UInt32 := do
  try
    let result ← match args with
      | ["--help"] | [] => pure (.ok usage)
      | ["debugger"] => Debugger.startDebugger; pure (.ok "Debugger stopped.")
      | ["debugger", port] => do
        let some n := port.toNat? | pure (.error "invalid port")
        if n == 0 || n > 65535 then pure (.error "invalid port")
        else Debugger.startDebugger n.toUInt16; pure (.ok "Debugger stopped.")
      | ["eval", source] => pure do
        let t ← elaborate (← Parser.parseExpr source)
        let n ← normalize t
        pure n.pretty
      | ["type", source] => pure do
        let t ← elaborate (← Parser.parseExpr source)
        pure (← inferType t).pretty
      | [command, path] =>
        if !["parse", "elab", "check"].contains command then
          pure (.error usage)
        else
          let source ← IO.FS.readFile path
          pure do
            let ds ← Parser.parseProgram source
            if command == "parse" then return reprStr ds
            let core ← elaborateProgram ds
            if command == "elab" then return String.intercalate "\n" (core.map CoreDecl.pretty)
            let ctx ← checkProgram core
            return s!"Checked {ctx.signatures.length} definition(s)."
      | _ => pure (.error usage)
    match result with
    | .ok output => IO.println output; pure 0
    | .error e => (← IO.getStderr).putStrLn s!"error: {e}"; pure 1
  catch e =>
    (← IO.getStderr).putStrLn s!"error: {e}"
    pure 1
