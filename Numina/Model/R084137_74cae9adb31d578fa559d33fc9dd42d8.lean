import Mathlib

theorem algebra_1628 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : 1 / a + 1 / b + 2 * (a + b) / (a ^ 2 + b ^ 2) = 0) : a / b = -1 := by
  have h1 : a ^ 2 + b ^ 2 ≠ 0 := by
    by_contra h2
    have h3 : a ^ 2 ≥ 0 := sq_nonneg a
    have h4 : b ^ 2 ≥ 0 := sq_nonneg b
    have h5 : a ^ 2 = 0 := by linarith [h2, h3, h4]
    have h6 : a = 0 := pow_eq_zero h5
    contradiction
  have eq1 : 1 / a + 1 / b + 2 * (a + b) / (a ^ 2 + b ^ 2) = 
    (b * (a ^ 2 + b ^ 2) + a * (a ^ 2 + b ^ 2) + 2 * (a + b) * (a * b)) / (a * b * (a ^ 2 + b ^ 2)) := by
    field_simp [ha, hb, show a ^ 2 + b ^ 2 ≠ 0 by apply h1]
    ring
  rw [eq1] at h
  have h2 : b * (a ^ 2 + b ^ 2) + a * (a ^ 2 + b ^ 2) + 2 * (a + b) * (a * b) = 0 := by
    have h3 : a * b * (a ^ 2 + b ^ 2) ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha
      exact hb
      exact h1
    field_simp [h3] at h ⊢
    linarith
  have h3 : (a + b) ^ 3 = 0 := by
    ring_nf at h2 ⊢
    linarith
  have h4 : a + b = 0 := by
    have h5 : (a + b) ^ 3 = 0 := h3
    simp at h5 ⊢
    all_goals
      nlinarith
  have h5 : a = -b := by
    linarith
  have h6 : a / b = -1 := by 
    field_simp [hb]
    linarith [h5]
  exact h6