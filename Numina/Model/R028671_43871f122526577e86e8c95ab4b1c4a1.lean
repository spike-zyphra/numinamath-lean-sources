import Mathlib

def f (n : ℕ) := Even n ∧ n > 0

theorem number_theory_316219 :
    ∃ n, f n ∧ n = 2006 := by
  use 2006
  constructor
  · -- Show that 2006 is even and positive
    constructor
    · -- Show that 2006 is even
      exact Nat.even_iff.mpr (by norm_num)
    · -- Show that 2006 is positive
      norm_num
  · -- Trivial: n = 2006
    rfl