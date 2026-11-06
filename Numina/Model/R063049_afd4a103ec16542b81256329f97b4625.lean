import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_325546 :
  IsLeast {x | ∃ a b : ℝ, x = a + b ∧ ∀ t : ℝ, a * cos t + b * cos (2 * t) ≥ -1} (-1) := by
  constructor
  · -- Show that -1 can be achieved
    use -1, 0
    constructor
    · norm_num
    · intro t
      have h1 : cos t ≤ 1 := by apply cos_le_one
      have h2 : -cos t ≥ -1 := by linarith
      simp [show cos (2 * t) = 2 * cos t ^ 2 - 1 from by rw [cos_two_mul]] 
      nlinarith [cos_le_one t, sq_nonneg (cos t - 1), Real.sin_sq_add_cos_sq t]
  · -- Show that -1 is the minimum
    intro x hx
    rcases hx with ⟨a, b, h_eq, h_ineq⟩
    have h1 := h_ineq 0
    have hcos0 : cos (0 : ℝ) = 1 := by simp
    rw [hcos0] at h1
    have hcos1 : cos (2 * (0 : ℝ)) = 1 := by norm_num [cos_zero]
    rw [hcos1] at h1
    have : a + b ≥ -1 := by linarith
    linarith [h_eq, this]