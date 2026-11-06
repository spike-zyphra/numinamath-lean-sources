import Mathlib

def f (n : ℕ) := ∑ i ∈ Finset.range n, (i + 1)

theorem number_theory_291323 : ∃ k, 2019 ∈ Finset.Icc (f k) (f (k + 1)) := by
  use 63
  native_decide