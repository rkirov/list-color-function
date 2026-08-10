/-
Dumps every constant name in the environment, for `scripts/check_refs.py`.
Run with:  lake env lean --run scripts/DumpNames.lean > /tmp/names.txt
-/
import Monophilic
open Lean

def main : IO Unit := do
  let env ← importModules #[{ module := `Monophilic }] {} (trustLevel := 0)
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    if !n.isInternal then out := out.push n.toString
  IO.println (String.intercalate "\n" out.toList)
