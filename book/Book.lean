import VersoManual
import Book.Papers
import Book.Map
import Book.Colouring
import Book.Polynomial
import Book.Lists
import Book.Chordal
import Book.Theorem1
import Book.TwoChoosable
import Book.TwoECC
import Book.Threshold
import Book.ReadingChallenge
import Book.Counting
import Book.Cliques
import Book.Paths
import Book.Swapping
import Book.Cycles
import Book.Cores
import Book.Theta
import Book.NotChoosable
import Book.Findings
import Book.Reference

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
{citep kirovNaimi}[] call a graph *`n`-monophilic* when the intuition holds for it — the name the
literature settled on is *enumeratively chromatic-choosable at `n`*, and that is the name used
throughout this book and the development. They prove that every cycle is enumeratively
chromatic-choosable at `n` for every `n`, characterize the graphs that are enumeratively
chromatic-choosable at `2`, and construct, for each `n`, a graph that is `n`-choosable but not
enumeratively chromatic-choosable at `n`.

This book accompanies a Lean 4 formalization of that paper. Every displayed statement below is
elaborated when the book is built, and each is discharged against the corresponding theorem in the
development — so what you read is what has been checked.

Their characterization at `n = 2` quotes one prior result, *Rubin's theorem*
{citep erdosRubinTaylor}[]: a connected graph is `2`-choosable exactly when its core is a
single vertex, an even cycle, or $`\theta_{2,2,2m}`. It is a theorem of 1980 that appears not to
have been machine-checked before. It is *proved* in this development
({ref "twochoosable"}[Which Graphs Are 2-Choosable?]), so Kirov and Naimi's Theorem 2 carries no
hypothesis here beyond connectivity. None of that mathematics is new; the proof is Rubin's own, and
the only novelty is that a machine has now been through it — which did turn up three points in his
three-page exposition that do not survive as printed.

It is written to be read in one direction, ending at a single file. The development's statement
surface is `comparator/Challenge.lean`: eleven theorems and the vocabulary they need, stated
exactly as the library states them, with the proofs removed. *Part I* is the path that makes that file readable
top to bottom, for a reader who is mathematically strong but has never met a chromatic polynomial.
It starts from what a proper colouring is ({ref "colouring"}[Colouring a Graph]) and proceeds
through the chromatic polynomial ({ref "polynomial"}[The Chromatic Polynomial]), list assignments
and enumerative chromatic-choosability ({ref "lists"}[Lists Instead of a Palette]), the first
positive answer ({ref "chordal"}[First Answers: Chordal Graphs]), the theorem about cycles
({ref "theorem1"}[Theorem 1: Cycles]), the two classifications at `n = 2`
({ref "twochoosable"}[Which Graphs Are 2-Choosable?] and
{ref "twoecc"}[Which Graphs Are Enumeratively Chromatic-Choosable at 2?]) and the eventual-agreement
theorem ({ref "threshold"}[Every Graph, Eventually]), to a guide to the file itself
({ref "readingchallenge"}[Reading `Challenge.lean`]). Part I states results and explains them; it
proves nothing.

*Part II* is the proofs, and is written for a different reader: someone who wants to know how a
counting argument in graph theory is set up in a proof assistant so that the counting stays
tractable. It covers how to count list colourings at all, the cone construction, the arithmetic on
paths, the swapping lemma that makes minimizing assignments rigid, the assembly into Theorem 1, and
the material on cores and theta graphs. It then collects what mechanization taught us that reading
did not — which hypotheses turned out to be load-bearing, which turned out to be unnecessary, which
pieces of surrounding folklore did not survive checking, which hypotheses of *our own* turned out to
be false, and the three corrections to Rubin's published argument. It closes with
{ref "reference"}[The Declarations]: the vocabulary and the headline results rendered straight out
of the library, with their own documentation.

A word on what "verified" means here and what it does not. The development contains no `sorry`, and
every result cited in this book depends only on Lean's three standard axioms — propositional
extensionality, choice, and quotient soundness. That is a strong guarantee about the proofs. It is
not a guarantee that the *statements* say what you think they say; that is what the numerical
cross-checks scattered through the development, and the discussion in this book, are for.

{include 1 Book.Map}

{include 1 Book.Colouring}

{include 1 Book.Polynomial}

{include 1 Book.Lists}

{include 1 Book.Chordal}

{include 1 Book.Theorem1}

{include 1 Book.TwoChoosable}

{include 1 Book.TwoECC}

{include 1 Book.Threshold}

{include 1 Book.ReadingChallenge}

{include 1 Book.Counting}

{include 1 Book.Cliques}

{include 1 Book.Paths}

{include 1 Book.Swapping}

{include 1 Book.Cycles}

{include 1 Book.Cores}

{include 1 Book.Theta}

{include 1 Book.NotChoosable}

{include 1 Book.Findings}

{include 1 Book.Reference}
