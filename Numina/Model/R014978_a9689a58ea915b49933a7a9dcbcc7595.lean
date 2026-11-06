import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_193852 :
  IsLeast {C : ℝ | ∀ x y z : ℝ, x + y + z = -1 → |x^3 + y^3 + z^3 + 1| ≤ C * |x^5 + y^5 + z^5 + 1|} (9 / 10) := by
  constructor
  · -- Show that 9/10 is in the set
    intro x y z h
    have h1 : z = -1 - x - y := by linarith
    have h14 : |x^3 + y^3 + z^3 + 1| ≤ (9 / 10) * |x^5 + y^5 + z^5 + 1| := by
      have h10 : z = -1 - x - y := by linarith
      rw [h10]
      cases' abs_cases (x^3 + y^3 + (-1 - x - y)^3 + 1) with h h <;>
      cases' abs_cases (x^5 + y^5 + (-1 - x - y)^5 + 1) with k k <;>
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - (-1 - x - y)), sq_nonneg (y - (-1 - x - y)), 
          sq_nonneg (x + 1 / 3), sq_nonneg (y + 1 / 3), sq_nonneg ((-1 - x - y) + 1 / 3),
          sq_nonneg (x + y + (-1 - x - y) + 1), sq_nonneg (x^2 + y^2 + (-1 - x - y)^2 - 1 / 3),
          sq_nonneg (x * y * ((-1 - x - y)) - 1 / 27)]
    linarith
  · -- Show that 9/10 is the least
    intro C hC
    have h1 : ∀ x y z : ℝ, x + y + z = -1 → |x^3 + y^3 + z^3 + 1| ≤ C * |x^5 + y^5 + z^5 + 1| := hC
    have h2 := h1 (-1/3 : ℝ) (-1/3 : ℝ) (-1/3 : ℝ) (by norm_num)
    norm_num [abs_of_nonneg] at h2 ⊢
    all_goals linarith