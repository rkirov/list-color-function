/-
Book generator.

Run through the interpreter (there is deliberately no `lean_exe` — see `lakefile.lean`):

    lake env lean --run Main.lean -- --output _out --depth 2 --without-tex

Then serve the result; Verso's HTML fetches a JSON side-file for code hovers, so opening
`index.html` directly from disk does not work:

    python3 -m http.server 8000 --directory _out/html-multi
-/
import VersoManual
import Book

open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  manualMain (%doc Book) (options := args)
