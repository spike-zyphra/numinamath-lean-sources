import Mathlib

theorem algebra_22106 {a b c : ℝ} (h₀ : a / b = Real.sqrt 10 / Real.sqrt 21) (h₁ : b / c = Real.sqrt 135 / Real.sqrt 8) (hn : b ≠ 0 ∧ c ≠ 0) :
    a / c = 15 * Real.sqrt 7 / 14 := by
  have hb : b ≠ 0 := hn.1
  have hc : c ≠ 0 := hn.2
  have h2 : a / c = (a / b) * (b / c) := by
    field_simp [hb, hc]
  rw [h2, h₀, h₁]
  have h3 : Real.sqrt 10 / Real.sqrt 21 * (Real.sqrt 135 / Real.sqrt 8) = (15 * Real.sqrt 7 / 14) := by
    have h4 : Real.sqrt 10 / Real.sqrt 21 = Real.sqrt (10 / 21) := by
      field_simp [Real.sqrt_div]
    have h5 : Real.sqrt 135 / Real.sqrt 8 = Real.sqrt (135 / 8) := by
      field_simp [Real.sqrt_div]
    rw [h4, h5]
    have h6 : Real.sqrt (10 / 21) * Real.sqrt (135 / 8) = Real.sqrt ((10 / 21) * (135 / 8)) := by
      rw [← Real.sqrt_mul (by norm_num)]
    rw [h6]
    have h7 : (10 / 21 : ℝ) * (135 / 8) = (225 / 28 : ℝ) := by norm_num
    rw [h7]
    have h9 : Real.sqrt (225 / 28 : ℝ) = (15 / 14) * Real.sqrt 7 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h9]
    field_simp
    <;> ring_nf <;> norm_num
  linarith [h3]