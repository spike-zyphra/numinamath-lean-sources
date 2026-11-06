import Mathlib

open Finset


theorem number_theory_77603 :
    ∑ i ∈ range 1989, (-1 : ℝ) ^ i * (1989 - i) / (i + 2) =
    ∑ i ∈ range 995, (2 * i + 1 : ℝ) / (996 + i) := by
  norm_num
  <;> try { linarith }