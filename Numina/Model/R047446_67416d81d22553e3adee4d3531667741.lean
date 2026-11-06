import Mathlib

theorem algebra_22119 (g : ℤ → ℤ) (hg : g = fun x => x^3 - 14 * x^2 + 18 * x + 72) :
    ∃! x, g x = 0 ∧ x = 12 := by

  use 12
  constructor
  · -- Show that 12 is a root: g(12) = 0 and 12 = 12
    constructor
    · -- Calculate g(12)
      rw [hg]
      norm_num
    · -- Show that 12 = 12
      rfl
  · -- Show that 12 is unique
    intro x h
    rcases h with ⟨_, hx⟩
    exact hx