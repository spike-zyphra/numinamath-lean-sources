import Mathlib

theorem algebra_21650 {x y : ℝ} (h₀ : x + y = 13) (h₁ : x * y = 24) :
    Real.sqrt (x ^ 2 + y ^ 2) = 11 := by
  have h2 : x ^ 2 + y ^ 2 = 121 := by
    have h3 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by 
      linarith
    rw [h3, h₀, h₁]
    all_goals norm_num
  rw [h2]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num