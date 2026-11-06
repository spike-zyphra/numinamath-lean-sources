import Mathlib

def f (n : ℕ) := ∑ i in Finset.range n, (2 * i - 1)

theorem number_theory_150101 : ∃ n, 1991 ∈ Finset.Icc (f n) (f (n + 1)) := by

  use 45
  native_decide