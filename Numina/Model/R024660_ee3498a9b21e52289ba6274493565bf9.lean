import Mathlib

def f (n : ℕ) := ∑ i ∈ Finset.range n, (3 * i - 2)

theorem number_theory_198717 : ∃ n, 2018 ∈ Finset.Icc (f n) (f (n + 1)) := by 
  use 37
  native_decide