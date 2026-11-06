import Mathlib

def f (n : ℕ) := n * (n + 1)

theorem number_theory_322273 : ∃ n, 2003 ∈ Finset.Icc (f n) (f (n + 1)) := by
  use 44
  native_decide