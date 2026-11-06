import Mathlib

theorem algebra_172724 {a : ℝ} (ha : a ≠ 0) (h : 1 / a + abs a + 1 = 0) : a = (1 - Real.sqrt 5) / 2 := by 
  have h1 : a < 0 := by
    by_contra h1
    push_neg at h1
    have h2 : 1 / a ≥ 0 := by
      apply div_nonneg
      norm_num
      linarith
    have h3 : abs a ≥ 0 := abs_nonneg a
    have h4 : 1 / a + abs a + 1 ≥ 0 := by linarith
    linarith
  have h2 : abs a = -a := by
    rw [abs_of_neg h1]
  rw [h2] at h
  have h3 : a^2 - a - 1 = 0 := by
    field_simp [ha] at h
    nlinarith
  have h4 : a = (1 + Real.sqrt 5) / 2 ∨ a = (1 - Real.sqrt 5) / 2 := by
    have h4 : a^2 - a - 1 = 0 := h3
    have : a = (1 + Real.sqrt 5) / 2 ∨ a = (1 - Real.sqrt 5) / 2 := by
      have h5 : a^2 - a - 1 = 0 := h4
      have h6 : a^2 - a - 1 = (a - (1 + Real.sqrt 5) / 2) * (a - (1 - Real.sqrt 5) / 2) := by
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        linarith
      rw [h6] at h5
      cases mul_eq_zero.1 h5 with
      | inl h7 => left; linarith
      | inr h8 => right; linarith
    exact this
  cases h4 <;> linarith [Real.sqrt_pos.mpr (show (0:ℝ)<5 by norm_num)]
  