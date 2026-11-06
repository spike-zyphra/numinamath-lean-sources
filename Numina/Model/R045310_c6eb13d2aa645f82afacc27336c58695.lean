import Mathlib

theorem algebra_247611 {p : ℝ} (r₁ r₂ : ℝ)
    (h₁ : (r₁ - 19) * (r₁ - 83) = p) (h₂ : (r₂ - 19) * (r₂ - 83) = p)
    (h₃ : r₁ < r₂) :
    IsLeast {x | (x - r₁) * (x - r₂) = -p} 19 := by
  have h4 : r₁ + r₂ = 102 := by
    nlinarith [sq_pos_of_pos (show 0 < r₂ - r₁ by linarith), sq_nonneg (r₁ - r₂), sq_nonneg (r₁ - 83), sq_nonneg (r₂ - 19)]
  have h5 : r₁ * r₂ = 1577 - p := by
    nlinarith [sq_pos_of_pos (show 0 < r₂ - r₁ by linarith), sq_nonneg (r₁ - r₂), sq_nonneg (r₁ - 83), sq_nonneg (r₂ - 19)]
  constructor
  · -- Show that 19 is in the set.
    rw [Set.mem_setOf_eq]
    nlinarith [h4, h5]
  · -- Show that 19 is the smallest element in the set.
    intro x hx
    rw [Set.mem_setOf_eq] at hx
    have eq1 : (x - 19) * (x - 83) = 0 := by
      nlinarith [sq_nonneg (x - 19), sq_nonneg (x - 83), h4, h5, hx]
    cases' (mul_eq_zero.mp eq1) with h7 h8
    · -- Case where `x - 19 = 0`, or `x = 19`
      linarith
    · -- Case where `x - 83 = 0`, or `x = 83`
      linarith