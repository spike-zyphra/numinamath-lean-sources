import Mathlib

def f (n : ℕ) := n * (n + 1)

theorem number_theory_297830 : ∃ n, 2009 ∈ Finset.Icc (f n) (f (n + 1)) := by
  use 44
  native_decide