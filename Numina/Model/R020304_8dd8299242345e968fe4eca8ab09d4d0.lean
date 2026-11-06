import Mathlib

theorem algebra_2309 {a b : ℝ} (hb : b ≠ 0) (ha : a / b = 19) :
    (a ^ 2 + a * b + b ^ 2) / (a ^ 2 - b ^ 2) = 1 + 7 / 120 := by
  have h1 : a = 19 * b := by
    field_simp [hb] at ha
    linarith
  have h2 : a ^ 2 + a * b + b ^ 2 = 381 * b ^ 2 := by
    rw [h1]
    ring_nf
  have h3 : a^2 - b^2 = 360 * b ^ 2 := by
    rw [h1]
    ring_nf
  have h4 : (a ^ 2 + a * b + b ^ 2) / (a ^ 2 - b ^ 2) = (381 * b ^ 2) / (360 * b ^ 2) := by
    rw [show a ^ 2 + a * b + b ^ 2 = 381 * b ^ 2 by exact h2]
    rw [show a ^ 2 - b ^ 2 = 360 * b ^ 2 by exact h3]
  have h5 : (381 * b ^ 2) / (360 * b ^ 2) = 381 / 360 := by
    have hb2 : b ^ 2 ≠ 0 := by
      apply pow_ne_zero 2
      exact hb
    field_simp [hb2]
    <;> ring_nf <;> field_simp
  have h6 : (381 : ℝ) / (360 : ℝ) = (127 : ℝ) / (120 : ℝ) := by norm_num
  have h7 : (127 : ℝ) / (120 : ℝ) = 1 + 7 / 120 := by norm_num
  rw [h4, h5, h6, h7]
  <;> ring_nf <;> field_simp
  <;> ring_nf <;> field_simp
  <;> norm_num