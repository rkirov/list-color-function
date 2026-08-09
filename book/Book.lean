import VersoManual
import Book.Papers
import Book.Map
import Book.Counting
import Book.Cliques
import Book.Paths
import Book.Swapping
import Book.Cycles
import Book.Cores
import Book.Theta
import Book.NotChoosable
import Book.Findings

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true

#doc (Manual) "Counting List Colorings" =>

%%%
authors := ["A verified companion to Kirov and Naimi"]
%%%

Give each vertex of a graph its own list of `n` permitted colors and count the proper colorings that
respect those lists. Intuitively, if you want to make that count small you should hand every vertex
the *same* list — sameness is what creates conflicts. For many graphs that intuition is correct.
For some it is false.

Kostochka and Sidorenko {citep kostochkaSidorenko}[] raised the question in 1990. Kirov and Naimi
{citep kirovNaimi}[] call a graph **`n`-monophilic** when the intuition holds for it, prove that
every cycle is `n`-monophilic for every `n`, characterize the `2`-monophilic graphs, and construct,
for each `n`, a graph that is `n`-choosable but not `n`-monophilic.

This book accompanies a Lean 4 formalization of that paper. It is written for two audiences at once:
a combinatorialist who wants to know what the mechanized proofs actually say, and a Lean user who
wants to see how a counting argument in graph theory is set up so that the counting stays tractable.
Every displayed statement below is elaborated when the book is built, and each is discharged against
the corresponding theorem in the development — so what you read is what has been checked.

The order of business is: how to count list colorings in a proof assistant at all
({ref "counting"}[Chapter 1]); the cheapest real theorem and what it costs
({ref "cliques"}[Chapter 2]); paths, where all the arithmetic lives ({ref "paths"}[Chapter 3]); the
swapping lemma that makes minimizing assignments rigid ({ref "swapping"}[Chapter 4]); and the
assembly into Theorem 1 ({ref "cycles"}[Chapter 5]). The last chapter
({ref "findings"}[Chapter 6]) collects what mechanization taught us that reading did not — which
hypotheses turned out to be load-bearing, which turned out to be unnecessary, and which pieces of
surrounding folklore did not survive checking.

A word on what "verified" means here and what it does not. The development contains no `sorry`, and
every result cited in this book depends only on Lean's three standard axioms — propositional
extensionality, choice, and quotient soundness. That is a strong guarantee about the proofs. It is
not a guarantee that the *statements* say what you think they say; that is what the numerical
cross-checks scattered through the development, and the discussion in this book, are for.

{include 1 Book.Map}

{include 1 Book.Counting}

{include 1 Book.Cliques}

{include 1 Book.Paths}

{include 1 Book.Swapping}

{include 1 Book.Cycles}

{include 1 Book.Cores}

{include 1 Book.Theta}

{include 1 Book.NotChoosable}

{include 1 Book.Findings}
