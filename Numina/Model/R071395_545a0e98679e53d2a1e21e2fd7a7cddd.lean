import Mathlib

theorem algebra_172784 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : 1 / a + 1 / b + 2 * (a + b) / (a ^ 2 + b ^ 2) = 0) : a / b = -1 := by
  have h1 : a ^ 2 + b ^ 2 ≠ 0 := by
    by_contra h2
    have h3 : a ^ 2 ≥ 0 := sq_nonneg a
    have h4 : b ^ 2 ≥ 0 := sq_nonneg b
    have h5 : a ^ 2 = 0 := by linarith [h2, h3, h4]
    have h6 : a = 0 := pow_eq_zero h5
    contradiction
  have eq1 : b * (a ^ 2 + b ^ 2) + a * (a ^ 2 + b ^ 2) + 2 * a * b * (a + b) = 0 := by
    have h2 : a ^ 2 + b ^ 2 ≠ 0 := h1
    field_simp [ha, hb, h2] at h ⊢
    nlinarith
  have eq2 : (a + b) ^ 3 = 0 := by
    ring_nf at eq1 ⊢
    linarith
  have eq3 : a + b = 0 := by
    have h1 : (a + b) ^ 3 = 0 := eq2
    simp at h1 
    linarith
  have eq4 : a = -b := by linarith 
  field_simp [hb, eq4]
  <;> nlinarith