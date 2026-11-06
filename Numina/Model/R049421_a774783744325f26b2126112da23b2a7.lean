import Mathlib

theorem algebra_307719 (a b c : ℝ) (h₀ : a * b = 10) (h₁ : a ^ 2 + b ^ 2 = c ^ 2) :
    |c| ≥ 2 * Real.sqrt 5 := by
  have h2 : a ^ 2 + b ^ 2 ≥ 20 := by
    nlinarith [sq_nonneg (a - b), h₀, sq_nonneg (a * b - 10)]
  have h3 : c ^ 2 ≥ 20 := by
    linarith [h₁, h2]
  have h4 : Real.sqrt (c ^ 2) ≥ Real.sqrt 20 := Real.sqrt_le_sqrt (show c ^ 2 ≥ (20 : ℝ) by linarith [h3])
  have h5 : Real.sqrt (c ^ 2) = |c| := by
    rw [Real.sqrt_sq_eq_abs]
  have h6 : Real.sqrt 20 = 2 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  linarith [h4, h5, h6]