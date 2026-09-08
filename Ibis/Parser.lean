import Ibis.Syntax

namespace Ibis.Parser

structure Token where
  text : String
  line : Nat
  column : Nat
  quoted : Bool := false
  deriving Repr, Inhabited

private def identStart (c : Char) : Bool := c.isAlpha || c == '_'
private def identRest (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

private partial def stringChars : List Char → List Char → Except String (String × List Char × Nat)
  | [], _ => .error "unterminated string"
  | '"' :: cs, acc => .ok (String.ofList acc.reverse, cs, 1)
  | '\n' :: _, _ => .error "newline in string literal"
  | '\\' :: c :: cs, acc => do
    let c' ← match c with
      | 'n' => pure '\n' | 'r' => pure '\r' | 't' => pure '\t'
      | '\\' => pure '\\' | '"' => pure '"'
      | _ => throw s!"unknown string escape: {c}"
    let (s, rest, n) ← stringChars cs (c' :: acc)
    pure (s, rest, n + 2)
  | c :: cs, acc => do
    let (s, rest, n) ← stringChars cs (c :: acc)
    pure (s, rest, n + 1)

private partial def blockComment (depth : Nat) (cs : List Char) (line col : Nat) :
    Except String (List Char × Nat × Nat) :=
  match cs with
  | [] => .error s!"{line}:{col}: unterminated block comment"
  | '{' :: '-' :: rest => blockComment (depth + 1) rest line (col + 2)
  | '-' :: '}' :: rest => if depth == 1 then .ok (rest, line, col + 2)
      else blockComment (depth - 1) rest line (col + 2)
  | '\n' :: rest => blockComment depth rest (line + 1) 1
  | _ :: rest => blockComment depth rest line (col + 1)

private partial def lexChars (cs : List Char) (line col : Nat) : Except String (List Token) := do
  match cs with
  | [] => pure [{ text := "<eof>", line, column := col }]
  | '\n' :: rest => return { text := "\n", line, column := col } :: (← lexChars rest (line + 1) 1)
  | '-' :: '-' :: rest => lexChars (rest.dropWhile (· != '\n')) line col
  | '{' :: '-' :: rest =>
    let (rest, l, c) ← blockComment 1 rest line (col + 2)
    let ts ← lexChars rest l c
    pure (if l > line then { text := "\n", line, column := col } :: ts else ts)
  | '"' :: rest =>
    let (s, rest, n) ← stringChars rest []
    return { text := s, line, column := col, quoted := true } :: (← lexChars rest line (col + n + 1))
  | c :: rest =>
    if c.isWhitespace then return ← lexChars rest line (col + 1)
    let (word, tail) ← if identStart c then
        let more := rest.takeWhile identRest
        pure (c :: more, rest.drop more.length)
      else if c.isDigit then
        let digits := rest.takeWhile Char.isDigit
        let tail := rest.drop digits.length
        match tail with
        | '.' :: d :: ds =>
          if d.isDigit then
            let frac := ds.takeWhile Char.isDigit
            pure (c :: digits ++ ['.', d] ++ frac, ds.drop frac.length)
          else pure (c :: digits, tail)
        | _ => pure (c :: digits, tail)
      else
        let ops := ["==>", "<$>", "<*>", ">>=", ":=", "=>", "->", "<-", "::", "<=", ">=", "==", "~=", "!=", "/Sigma", "/Pi"]
        match ops.find? (fun s => s.toList.isPrefixOf cs) with
        | some op => pure (op.toList, cs.drop op.length)
        | none =>
          if "()[]{},;:.@?=+-*/<>|ΠΣλ→".contains c then pure ([c], rest)
          else throw s!"{line}:{col}: unexpected character '{c}'"
    return { text := String.ofList word, line, column := col } :: (← lexChars tail line (col + word.length))

def lex (source : String) : Except String (List Token) := lexChars source.toList 1 1

structure State where
  tokens : List Token
  nesting : Nat := 0
  deriving Inhabited

abbrev P := StateT State (Except String)

private def skipNL : P Unit := modify fun s => { s with tokens := s.tokens.dropWhile (fun t => t.text == "\n") }
private def peek : P Token := do
  if (← get).nesting > 0 then skipNL
  pure ((← get).tokens.headD { text := "<eof>", line := 0, column := 0 })
private def pop : P Token := do
  let t ← peek
  modify fun s => { s with tokens := s.tokens.drop 1 }
  pure t
private def fail (msg : String) : P α := do
  let t ← peek
  throw s!"{t.line}:{t.column}: {msg}; found '{t.text}'"
private def isAt (s : String) : P Bool := do
  let t ← peek
  pure (!t.quoted && t.text == s)
private def eat (s : String) : P Bool := do
  if ← isAt s then let _ ← pop; pure true else pure false
private def expect (s : String) : P Unit := do
  unless ← eat s do fail s!"expected '{s}'"
private def attempt (p : P α) : P (Option α) := fun s =>
  match p s with
  | .ok (a, s') => .ok (some a, s')
  | .error _ => .ok (none, s)

private def reserved : List String :=
  ["Type", "Prop", "def", "struct", "inductive", "site", "where", "cover", "has", "import", "as", "exposing",
   "if", "then", "else", "for", "match", "with", "let", "in", "do", "end", "fun", "by", "qed", "to",
   "and", "or", "not", "class", "instance", "intro", "exact", "apply", "rfl", "simp", "cases", "induction",
   "bind", "have", "show", "sorry", "path_across", "covers", "lan", "glue"]
private def ident : P String := do
  let t ← peek
  if !t.quoted && t.text.toList.head?.any identStart && !reserved.contains t.text then
    let _ ← pop
    pure t.text
  else fail "expected an identifier"

private def literal? (t : Token) : Option Literal :=
  if t.quoted then some (.string t.text)
  else if t.text == "true" then some (.bool true)
  else if t.text == "false" then some (.bool false)
  else match t.text.toInt? with
    | some n => some (.int n)
    | none => if t.text.toList.head?.any Char.isDigit && t.text.contains '.' then
        match t.text.splitOn "." with
        | [a, b] => do
          let a ← a.toNat?
          let n ← b.toNat?
          pure (.float (a.toFloat + n.toFloat / (10 ^ b.length).toFloat))
        | _ => none else none

private def binPrec : String → Option (Nat × Bool)
  | "->" | "→" => some (1, true)
  | ">>=" => some (2, false)
  | "==>" => some (3, true)
  | "or" => some (4, false)
  | "and" => some (5, false)
  | "<$>" | "<*>" => some (6, false)
  | "<=" | ">=" | "<" | ">" | "==" | "~=" | "!=" => some (7, false)
  | "+" | "-" => some (8, false)
  | "*" | "/" => some (9, false)
  | "." => some (10, true)
  | _ => none

private def atomStart (t : Token) : Bool :=
  t.quoted || (literal? t).isSome || ["(", "[", "@", "?", "Type", "Prop"].contains t.text ||
    (t.text.toList.head?.any identStart && !reserved.contains t.text)

private def tupleTerm : List Term → Term
  | [] => .unit
  | [t] => t
  | t :: ts => .pair t (tupleTerm ts)

mutual
  partial def expr (minPrec : Nat := 0) : P Term := do
    let lhs ← parsePrefix
    restExpr lhs minPrec

  private partial def restExpr (lhs : Term) (minPrec : Nat) : P Term := do
    let t ← peek
    if let some (prec, right) := binPrec t.text then
      if prec < minPrec then return lhs
      let _ ← pop
      skipNL
      let rhs ← expr (if right then prec else prec + 1)
      let term := if t.text == "->" || t.text == "→" then Term.pi "_" lhs rhs else .binop t.text lhs rhs
      if prec == 7 then
        if (binPrec (← peek).text).any (fun x => x.1 == 7) then fail "comparison operators do not associate"
      restExpr term minPrec
    else if minPrec ≤ 11 && atomStart t then
      let arg ← atom
      restExpr (.app lhs arg) minPrec
    else pure lhs

  private partial def parsePrefix : P Term := do
    if ← eat "let" then
      let n ← ident
      let ty ← if ← eat ":" then some <$> expr else pure none
      expect "="
      let e ← expr
      expect "in"
      skipNL
      return .letE n ty e (← expr)
    if ← eat "if" then
      let c ← expr
      expect "then"
      let t ← expr
      expect "else"
      return .ifE c t (← expr)
    if ← eat "fun" <||> eat "λ" then
      let mut ns := [← ident]
      while !(← isAt "=>") do ns := ns ++ [← ident]
      expect "=>"
      skipNL
      let b ← expr
      return ns.foldr Term.lam b
    if ← eat "for" then
      let n ← ident
      expect "in"
      let xs ← expr
      expect "do"
      return .forE n xs (← expr)
    if ← eat "match" then
      let e ← expr
      expect "with"
      let mut bs := []
      skipNL
      while ← eat "|" do
        let p ← pattern
        unless ← eat "->" <||> eat "→" do fail "expected branch arrow"
        let b ← expr
        bs := bs ++ [(p, b)]
        skipNL
      if bs.isEmpty then fail "expected a match branch"
      return .matchE e bs
    if ← eat "do" then
      let braced ← eat "{"
      skipNL
      let mut es := []
      while !(← isAt (if braced then "}" else "end")) do
        if ← isAt "<eof>" then fail "unterminated do block (use braces or end)"
        let binding ← attempt do let n ← ident; expect "<-"; pure n
        let e ← expr
        es := es ++ [match binding with | some n => .bind n e | none => e]
        if !(← isAt (if braced then "}" else "end")) then
          unless ← eat ";" <||> eat "\n" do fail "expected do statement separator"
          skipNL
      let _ ← pop
      return .doE es
    if ← eat "fst" then return .fst (← atom)
    if ← eat "snd" then return .snd (← atom)
    if ← eat "Cover" then return .cover (← atom) (← atom)
    if ← eat "Sect" then return .sect (← atom) (← atom)
    if ← eat "res" then
      let s ← atom
      expect "to"
      return .res s (← atom)
    if ← eat "ext" then
      let s ← atom
      let u ← atom
      unless ← eat "->" <||> eat "→" do fail "expected extension arrow"
      return .ext s u (← atom)
    if ← eat "-" then return .unop "-" (← expr 11)
    if ← eat "not" then return .unop "not" (← expr 11)
    if ← eat "Σ" <||> eat "/Sigma" then
      let (n, t) ← binder
      expect ","
      return .sigma n t (← expr)
    if ← eat "Π" <||> eat "/Pi" then
      let (n, t) ← binder
      unless ← eat "->" <||> eat "→" do fail "expected dependent function arrow"
      return .pi n t (← expr)
    let dep ← attempt do
      let b ← binder
      unless ← eat "->" <||> eat "→" do fail "expected arrow"
      pure b
    if let some (n, t) := dep then return .pi n t (← expr)
    atom

  private partial def atom : P Term := do
    let t ← peek
    if let some l := literal? t then let _ ← pop; return .lit l
    if ← eat "Type" then
      let t ← peek
      if let some n := t.text.toNat? then
        if n == 0 then fail "Type 0 is reserved; use Prop"
        let _ ← pop
        return .universe (.level n)
      return .universe (.named (← ident))
    if ← eat "Prop" then return .universe (.level 0)
    if ← eat "@" then return .site (← ident)
    if ← eat "?" then
      let t ← pop
      match t.text.toNat? with
      | some n => return .mvar n
      | none => fail "expected numeric metavariable ID"
    if ← eat "(" then
      modify fun s => { s with nesting := s.nesting + 1 }
      let es ← separated ")"
      modify fun s => { s with nesting := s.nesting - 1 }
      return tupleTerm es
    if ← eat "[" then
      modify fun s => { s with nesting := s.nesting + 1 }
      let es ← separated "]"
      modify fun s => { s with nesting := s.nesting - 1 }
      return .list es
    let n ← ident
    return if n.toList.head?.any Char.isUpper then .const n else .var n

  private partial def separated (close : String) : P (List Term) := do
    if ← eat close then return []
    let mut e ← expr
    if ← eat ":" then e := .ann e (← expr)
    if ← eat "," then return e :: (← separated close)
    expect close
    pure [e]

  private partial def binder : P Param := do
    expect "("
    modify fun s => { s with nesting := s.nesting + 1 }
    let n ← ident
    expect ":"
    let t ← expr
    expect ")"
    modify fun s => { s with nesting := s.nesting - 1 }
    pure (n, t)

  partial def pattern : P Pat := do
    let t ← peek
    if let some l := literal? t then let _ ← pop; return .lit l
    if ← eat "(" then
      let p ← pattern
      let mut ps := [p]
      while ← eat "," do ps := ps ++ [← pattern]
      expect ")"
      return if ps.length == 1 then p else .tuple ps
    let n ← ident
    if ← eat "::" then return .partition n (← pattern)
    if n == "_" then return .wildcard
    if n.toList.head?.any Char.isUpper then
      let mut ps := []
      while atomStart (← peek) do ps := ps ++ [← pattern]
      return .ctor n ps
    pure (.capture n)
end

private partial def telescope : P (List Param) := do
  if ← isAt "(" then return (← binder) :: (← telescope)
  pure []

private def tactics : P (List Tactic) := do
  expect "by"
  skipNL
  let mut ts := []
  while !(← isAt "qed") do
    let name := (← pop).text
    let t ← match name with
      | "intro" => Tactic.intro <$> ident
      | "exact" => Tactic.exact <$> expr
      | "apply" => Tactic.apply <$> expr
      | "rfl" => pure .rfl
      | "simp" => Tactic.simp <$> expr
      | "cases" => Tactic.cases <$> expr
      | "induction" => Tactic.induction <$> expr
      | "show" => Tactic.showE <$> expr
      | "sorry" => pure .admit
      | "bind" | "have" => do
        let n ← ident
        let ty ← if ← eat ":" then some <$> expr else pure none
        expect "="
        let e ← expr
        pure (if name == "bind" then .bind n ty e else .haveE n ty e)
      | "path_across" => do pure (Tactic.pathAcross (← atom) (← atom))
      | "covers" => do pure (Tactic.covers (← atom) (← atom))
      | "res" => do pure (Tactic.res (← atom) (← atom))
      | "lan" => do pure (Tactic.lan (← atom) (← atom))
      | "glue" => do pure (Tactic.glue (← atom) (← atom) (← atom) (← atom))
      | _ => fail s!"unknown tactic '{name}'"
    ts := ts ++ [t]
    let _ ← eat ";"
    skipNL
  expect "qed"
  pure ts

private def fields : P (List Param) := do
  skipNL
  let mut fs := []
  let mut more := true
  while more do
    let name ← attempt do
      let _ ← eat "|"
      let n ← ident
      expect ":"
      pure n
    match name with
    | none => more := false
    | some n =>
      fs := fs ++ [(n, ← expr)]
      let _ ← eat ";"
      skipNL
  pure fs

def decl : P Decl := do
  if ← eat "def" then
    let n ← ident
    let ps ← telescope
    expect ":"
    let ty ← expr
    expect ":="
    skipNL
    let b ← if ← isAt "by" then FunctionBody.tactics <$> tactics else FunctionBody.simple <$> expr
    return .function n ps ty b
  if ← eat "struct" then
    let n ← ident
    let ps ← telescope
    expect "where"
    return .struct n ps (← fields)
  if ← eat "inductive" then
    let n ← ident
    let ps ← telescope
    expect ":"
    let arity ← expr
    expect "where"
    return .inductiveE n ps arity (← fields)
  if ← eat "site" then
    let n ← ident
    expect "where"
    skipNL
    let mut rules := []
    while ← eat "cover" do
      expect "@"
      let parent ← ident
      expect "has"
      expect "{"
      let mut children := []
      unless ← isAt "}" do
        expect "@"
        children := [← ident]
        while ← eat "," do expect "@"; children := children ++ [← ident]
      expect "}"
      rules := rules ++ [{ parent := parent, children := children }]
      skipNL
    return .site n rules
  if ← eat "import" then
    let mut n ← ident
    while ← eat "." do n := n ++ "." ++ (← ident)
    if ← eat "as" then return .importE n (some (← ident))
    if ← eat "exposing" then
      expect "("
      let mut names := [← ident]
      while ← eat "," do names := names ++ [← ident]
      expect ")"
      return .importExposing n names
    return .importE n none
  return .term (← expr)

private def run (p : P α) (source : String) : Except String α := do
  let tokens ← lex source
  let (result, _) ← (do skipNL; let a ← p; skipNL; expect "<eof>"; pure a) { tokens }
  pure result

def parseExpr : String → Except String Term := run expr
def parseDecl : String → Except String Decl := run decl
def parseProgram : String → Except String (List Decl) := run do
  let mut ds := []
  while !(← isAt "<eof>") do
    ds := ds ++ [← decl]
    let _ ← eat ";"
    skipNL
  pure ds

end Ibis.Parser
