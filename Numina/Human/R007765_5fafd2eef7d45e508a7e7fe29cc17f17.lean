import Mathlib
open Mathlib

/--
Two is $10 \%$ of $x$ and $20 \%$ of $y$. What is $x - y$?
$(\mathrm {A}) \ 1 \qquad (\mathrm {B}) \ 2 \qquad (\mathrm {C})\ 5 \qquad (\mathrm {D}) \ 10 \qquad (\mathrm {E})\ 20$
-/

lemma algebra_1153 (x y : ℝ) (h1 : 2 = (10 : ℝ) / (100 : ℝ) * x) (h2 : 2 = (20 : ℝ) / (100 : ℝ) * y) : x - y = 10 := by
  linarith