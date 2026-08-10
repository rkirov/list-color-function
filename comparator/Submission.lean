import Monophilic
/-!
# Submission: the real development

The comparator matches the placeholder statements of `Challenge.lean` against declarations of the
same fully-qualified names in this module's environment. Every one of them is proved in the
`Monophilic` library of this repository, under exactly those names, so importing the library is the
whole submission — no re-export shim is needed, and none is wanted: a shim would put a second
declaration between the comparator and the thing that was actually proved.

`config.json` therefore sets `"solution_module": "Submission"`.
-/
