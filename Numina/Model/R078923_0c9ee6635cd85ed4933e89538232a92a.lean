import Mathlib

theorem algebra_301132 {a b : ℝ} (ha : a ≠ b)
    (h1 : a^2 - 4 * a + 1 = 0) (h2 : b^2 - 4 * b + 1 = 0) :
    1 / (a + 1) + 1 / (b + 1) = 1 := by
  have h3 : a + 1 ≠ 0 := by
    by_contra h
    have ha2 : a = -1 := by linarith
    rw [show a = -1 by linarith] at h1
    nlinarith
  have h4 : b + 1 ≠ 0 := by
    by_contra h
    have hb2 : b = -1 := by linarith
    rw [show b = -1 by linarith] at h2
    nlinarith
  have h5 : a + b = 4 := by
    have h4 : a^2 - b^2 - 4 * (a - b) = 0 := by linarith
    have h5 : (a - b) * (a + b - 4) = 0 := by
      ring_nf at h4 ⊢
      linarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- case $a - b = 0$, impossible
      exfalso
      exact ha (by linarith)
    · -- case $a + b - 4 = 0$, desired
      linarith
  have hab : a * b = 1 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne ha), h5]
  field_simp [(show a + 1 ≠ 0 by assumption), (show b + 1 ≠ 0 by assumption)]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne ha), h5, hab]