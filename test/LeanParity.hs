-- A dependency-light oracle for the working Haskell evaluator. Run through
-- test/lean-parity.py; the historical Cabal tests require additional packages.
module Main (main) where

import Ibis.AST.Core
import Ibis.AST.Surface (Literal (..), Pat (..))
import Ibis.Typecheck.Eval (eval, quoteInt)

int :: Integer -> CoreTerm
int = Lit . LitInt

fixtures :: [(String, CoreTerm)]
fixtures =
  [ ("Type 7", Universe 7)
  , ("Prop", Universe 0)
  , ("42", int 42)
  , ("true", Lit (LitBool True))
  , ("()", Unit)
  , ("(fun x => x) 7", App (Lam (Just "x") (Var 0)) (int 7))
  , ("(fun x => fun y => x) 11 22", App (App (Lam (Just "x") (Lam (Just "y") (Var 1))) (int 11)) (int 22))
  , ("let x = 3 in x", Let 0 (int 3) (Var 0))
  , ("let x = 3 in let y = 4 in x", Let 0 (int 3) (Let 0 (int 4) (Var 1)))
  , ("fst (1, 2)", Fst (Pair (int 1) (int 2)))
  , ("snd (1, 2)", Snd (Pair (int 1) (int 2)))
  , ("if true then 1 else 2", Match (Lit (LitBool True)) [(PLit (LitBool True), int 1), (PLit (LitBool False), int 2)])
  , ("match (5, 6) with | (x, y) -> x", Match (Pair (int 5) (int 6)) [(PTuple [PCapture "x", PCapture "y"], Var 1)])
  ]

render :: CoreTerm -> String
render (Universe 0) = "Prop"
render (Universe n) = "Type " ++ show n
render (Lit (LitInt n)) = show n
render (Lit (LitBool b)) = if b then "true" else "false"
render Unit = "()"
render other = error ("unexpected parity result: " ++ show other)

main :: IO ()
main = mapM_ (\(source, term) -> putStrLn (source ++ "\t" ++ render (quoteInt 0 (eval [] term)))) fixtures
