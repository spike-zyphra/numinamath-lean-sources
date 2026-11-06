import Mathlib

theorem algebra_180121 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a / b = 2 / 5) :
    a ^ 2 / (a * b + b ^ 2) = 4 / 35 := by 
  have ha_eq : a = (2 / 5) * b := by
    field_simp [hb] at h 
    linarith
  rw [ha_eq]
  have h1 : ((2 / 5 : ℝ) * b) ^ 2 / (((2 / 5 : ℝ) * b) * b + b ^ 2) = 4 / 35 := by
    have h2 : ((2 / 5 : ℝ) * b) ^ 2 = (4 / 25) * b ^ 2 := by 
      ring_nf 
    have h3 : ((2 / 5 : ℝ) * b) * b + b ^ 2 = (7 / 5) * b ^ 2 := by 
      ring_nf 
    rw [h2, h3] 
    have hb2 : b ^ 2 ≠ 0 := by 
      apply pow_ne_zero 
      exact hb 
    field_simp [hb2] 
    <;> ring_nf <;> field_simp <;> linarith 
  exact h1