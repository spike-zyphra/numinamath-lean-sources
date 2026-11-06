import Mathlib

theorem algebra_184340 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = 23 ∧ b = 22) :
    ((a^3 - a - 2 * b - b^2 / a) / ((1 - Real.sqrt (1 / a + b / a^2)) * (a + Real.sqrt (a + b)))) /
    ((a^3 + a^2 + a * b + a^2 * b) / (a^2 - b^2) + b / (a - b)) = 1 := by
  rcases h with ⟨ha_eq, hb_eq⟩
  have ha23 : a = (23 : ℝ) := by linarith
  have hb22 : b = (22 : ℝ) := by linarith
  rw [ha23, hb22]
  have h2 : Real.sqrt ((1 / (23 : ℝ) + (22 : ℝ) / (23 : ℝ) ^ 2)) = Real.sqrt (45 : ℝ) / 23 := by
    rw [show (1 / (23 : ℝ) + (22 : ℝ) / (23 : ℝ) ^ 2) = (45 : ℝ) / 529 by norm_num]
    have h3 : Real.sqrt ((45 : ℝ) / 529) = Real.sqrt (45 : ℝ) / 23 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    linarith
  have h4 : Real.sqrt ((23 + (22 : ℝ)) : ℝ) = Real.sqrt (45 : ℝ) := by norm_num
  rw [h2, h4]
  have h5 : (1 - Real.sqrt (45 : ℝ) / 23 : ℝ) * (23 + Real.sqrt (45 : ℝ)) = (484 / 23 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (45 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (45 : ℝ) by norm_num)]
  rw [h5]
  norm_num
  <;> nlinarith [Real.sqrt_nonneg (45 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (45 : ℝ) by norm_num)]