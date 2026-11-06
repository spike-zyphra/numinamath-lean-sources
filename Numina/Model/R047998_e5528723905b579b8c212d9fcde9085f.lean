import Mathlib

theorem inequalities_597275 (a b c : ℝ) (h₀ : a ≠ b) (h₁ : b ≠ c) (h₂ : c ≠ a) :
    a^2 / (b - c)^2 + b^2 / (c - a)^2 + c^2 / (a - b)^2 ≥ 2 := by
  have hx1 : a - b ≠ 0 := by intro h; apply h₀; linarith
  have hx2 : b - c ≠ 0 := by intro h; apply h₁; linarith
  have hx3 : c - a ≠ 0 := by intro h; apply h₂; linarith
  have hx4 : (a - b) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero hx1
  have hx5 : (b - c) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero hx2
  have hx6 : (c - a) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero hx3
  have h3 : a ^ 2 / (b - c) ^ 2 + b ^ 2 / (c - a) ^ 2 + c ^ 2 / (a - b) ^ 2 - 2 ≥ 0 := by
    have h4 : a ^ 2 / (b - c) ^ 2 + b ^ 2 / (c - a) ^ 2 + c ^ 2 / (a - b) ^ 2 - 2 =
        (a ^ 2 * (c - a) ^ 2 * (a - b) ^ 2 + b ^ 2 * (b - c) ^ 2 * (a - b) ^ 2 + c ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 - 2 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2) / ((b - c) ^ 2 * (c - a) ^ 2 * (a - b) ^ 2) := by
      field_simp [hx1, hx2, hx3]
      <;> ring
    rw [h4]
    apply div_nonneg
    nlinarith [sq_nonneg (a * (c - a) * (a - b) + b * (b - c) * (a - b) + c * (b - c) * (c - a)), sq_nonneg (a * (b - c) - b * (a - b)), sq_nonneg (b * (c - a) - c * (b - c)), sq_nonneg (a * (a - b) - c * (a - b)), sq_nonneg (a * (c - a) - c * (a - b)), sq_nonneg (b * (b - c) - a * (b - c)), sq_nonneg (b * (a - b) - a * (c - a)), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_pos_of_ne_zero hx1, sq_pos_of_ne_zero hx2, sq_pos_of_ne_zero hx3, mul_pos hx4 hx5, mul_pos hx4 hx6, mul_pos hx5 hx6]
    positivity
  linarith