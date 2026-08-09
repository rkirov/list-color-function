/-
Bibliography for the Kirov–Naimi verified companion.

Bibliographic data here has been checked against zbMATH, dblp and publisher DOIs; see
`references.md` in the repository root for the full verification notes.
-/
import VersoManual
open Verso.Genre.Manual

namespace Book

def kirovNaimi : Article where
  title := inlines!"List coloring and n-monophilic graphs"
  authors := #[inlines!"Radoslav Kirov", inlines!"Ramin Naimi"]
  journal := inlines!"Ars Combinatoria"
  month := none
  year := 2016
  volume := inlines!"124"
  number := inlines!""
  pages := some (329, 340)
  url := some "https://arxiv.org/abs/1004.5183"

def erdosRubinTaylor : Article where
  title := inlines!"Choosability in graphs"
  authors := #[inlines!"Paul Erdős", inlines!"Arthur L. Rubin", inlines!"Herbert Taylor"]
  journal := inlines!"Congressus Numerantium"
  month := none
  year := 1980
  volume := inlines!"26"
  number := inlines!""
  pages := some (125, 157)

def kostochkaSidorenko : Article where
  title := inlines!"Problem presented at the problem session, Fourth Czechoslovak Symposium on Combinatorics, Prachatice 1990"
  authors := #[inlines!"Alexandr V. Kostochka", inlines!"Alexander F. Sidorenko"]
  journal := inlines!"Annals of Discrete Mathematics"
  month := none
  year := 1992
  volume := inlines!"51"
  number := inlines!""
  pages := some (380, 380)

def donner : Article where
  title := inlines!"On the number of list-colorings"
  authors := #[inlines!"Q. Donner"]
  journal := inlines!"Journal of Graph Theory"
  month := none
  year := 1992
  volume := inlines!"16"
  number := inlines!"3"
  pages := some (239, 245)

def dirac : Article where
  title := inlines!"On rigid circuit graphs"
  authors := #[inlines!"Gabriel A. Dirac"]
  journal := inlines!"Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg"
  month := none
  year := 1961
  volume := inlines!"25"
  number := inlines!""
  pages := some (71, 76)

def thomassen : Article where
  title := inlines!"The chromatic polynomial and list colorings"
  authors := #[inlines!"Carsten Thomassen"]
  journal := inlines!"Journal of Combinatorial Theory, Series B"
  month := none
  year := 2009
  volume := inlines!"99"
  number := inlines!"2"
  pages := some (474, 479)

def wangQianYan : Article where
  title := inlines!"When does the list-coloring function of a graph equal its chromatic polynomial"
  authors := #[inlines!"Wei Wang", inlines!"Jianguo Qian", inlines!"Zhidan Yan"]
  journal := inlines!"Journal of Combinatorial Theory, Series B"
  month := none
  year := 2017
  volume := inlines!"122"
  number := inlines!""
  pages := some (543, 549)

def galvin : Article where
  title := inlines!"The list chromatic index of a bipartite multigraph"
  authors := #[inlines!"Fred Galvin"]
  journal := inlines!"Journal of Combinatorial Theory, Series B"
  month := none
  year := 1995
  volume := inlines!"63"
  number := inlines!"1"
  pages := some (153, 158)

def gutner : Article where
  title := inlines!"The complexity of planar graph choosability"
  authors := #[inlines!"Shai Gutner"]
  journal := inlines!"Discrete Mathematics"
  month := none
  year := 1996
  volume := inlines!"159"
  number := inlines!""
  pages := some (119, 130)

def kaulMudrock : Article where
  title := inlines!"On the chromatic polynomial and counting DP-colorings of graphs"
  authors := #[inlines!"Hemanshu Kaul", inlines!"Jeffrey A. Mudrock"]
  journal := inlines!"Advances in Applied Mathematics"
  month := none
  year := 2021
  volume := inlines!"123"
  number := inlines!""
  url := some "https://doi.org/10.1016/j.aam.2020.102131"

def vizingList : Article where
  title := inlines!"Coloring the vertices of a graph in prescribed colors"
  authors := #[inlines!"Vadim G. Vizing"]
  journal := inlines!"Metody Diskretnogo Analiza"
  month := none
  year := 1976
  volume := inlines!"29"
  number := inlines!""
  pages := some (3, 10)

def bhojaVizing : ArXiv where
  title := inlines!"A verified implementation of the Misra and Gries edge coloring algorithm"
  authors := #[inlines!"Arohee Bhoja"]
  year := 2025
  id := "2512.13999"

def gonthier4ct : Article where
  title := inlines!"Formal proof — the four-color theorem"
  authors := #[inlines!"Georges Gonthier"]
  journal := inlines!"Notices of the American Mathematical Society"
  month := none
  year := 2008
  volume := inlines!"55"
  number := inlines!"11"
  pages := some (1382, 1393)

def bauerNipkow : InProceedings where
  title := inlines!"The 5 colour theorem in Isabelle/Isar"
  authors := #[inlines!"Gertrud Bauer", inlines!"Tobias Nipkow"]
  year := 2002
  booktitle := inlines!"Theorem Proving in Higher Order Logics (TPHOLs 2002), LNCS 2410"

end Book
