import Mathlib

def f (n : ℕ) := Even n ∧ n > 0

theorem number_theory_204569 :
    ∃ c, f (2008 - c) ∧ c = 4 := by
  use 4
  constructor
  · -- Show that 2008 - 4 is even and greater than 0
    unfold f
    constructor
    · -- Show that 2008 - 4 is even
      native_decide
    · -- Show that 2008 - 4 > 0
      all_goals norm_num
  · -- Show that c = 4
    rfl