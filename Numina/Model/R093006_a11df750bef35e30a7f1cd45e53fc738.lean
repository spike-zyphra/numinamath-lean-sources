import Mathlib

theorem algebra_154739 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : a * b * c = 8) :
    1 / a + 1 / b + 1 / c < 0 := by
  have h2 : a ≠ 0 := by
    intro h
    have h3 : a * b * c = 0 := by
      simp [h]
    linarith
  have h3 : b ≠ 0 := by
    intro h
    have h4 : a * b * c = 0 := by
      simp [h]
    linarith
  have h4 : c ≠ 0 := by
    intro h
    have h5 : a * b * c = 0 := by
      simp [h]
    linarith
  have h5 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
    field_simp [h2, h3, h4]
    ring
  have h6 : b * c + a * c + a * b < 0 := by
    have hsq : (a + b + c) ^ 2 = 0 := by
      rw [h₀]
      norm_num
    have heq : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (b * c + a * c + a * b) := by ring
    have h7 : a^2 + b^2 + c^2 > 0 := by
      by_contra h
      push_neg at h
      have h14 : a^2 ≥ 0 := sq_nonneg a
      have h15 : b^2 ≥ 0 := sq_nonneg b
      have h16 : c^2 ≥ 0 := sq_nonneg c
      have h13 : a^2 = 0 := by linarith [h14, h15, h16, h]
      have h11 : b^2 = 0 := by linarith [h14, h15, h16, h]
      have h12 : c^2 = 0 := by linarith [h14, h15, h16, h]
      have ha0 : a = 0 := pow_eq_zero h13
      have hb0 : b = 0 := pow_eq_zero h11
      have hc0 : c = 0 := pow_eq_zero h12
      have hbc : a * b * c = 0 := by
        simp [ha0, hb0, hc0]
      linarith [h₁, hbc]
    nlinarith [hsq, heq, h7]
  have h7 : (b * c + a * c + a * b) / (a * b * c) < 0 := by
    apply div_neg_of_neg_of_pos (by linarith) (by nlinarith)
  linarith [h5, h7]