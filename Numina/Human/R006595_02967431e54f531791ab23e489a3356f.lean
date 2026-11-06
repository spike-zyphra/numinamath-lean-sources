import Mathlib

open Finset


theorem number_theory_638981
  (n : ℕ) (k : ℝ) (hn : n > 0) (a : ℕ → ℝ) (ha : ∀ i ∈ range n, 0 < a i) :
  (∏ i ∈ range n, a i) ^ k = ∏ i ∈ range n, (a i) ^ k := by 
  rw [Real.finset_prod_rpow]
  intro i hi
  obtain h1 := ha i hi
  linarith