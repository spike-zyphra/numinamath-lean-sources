import Mathlib

theorem algebra_202436 (m : ℝ) (z1 z2 : ℂ)
    (hz1 : z1 = 1 + 2 * .I) (hz2 : z2 = m + 3 * .I)
    (h : ∃ k : ℝ, (z1 / z2).re = 0 ∧ (z1 / z2).im = k) :
    Complex.abs (z1 + z2) = 5 * Real.sqrt 2 := by
  rcases h with ⟨k, hk1, hk2⟩
  rw [hz1, hz2] at hk1 hk2
  simp [Complex.div_re, Complex.div_im, Complex.normSq] at hk1 hk2
  have h2 : m ^ 2 + 9 > 0 := by
    nlinarith [sq_nonneg m]

  have hk3 : ((m + 6) / (m ^ 2 + 9) ) = 0 := by
    have eq1 : m / (m ^ 2 + 9) + (2 * 3) / (m ^ 2 + 9) = 0 := by
      field_simp [(show m * m + 3 * 3 = m ^ 2 + 9 by ring)] at hk1 ⊢
      linarith
    have eq2 : ((m + 6) / (m ^ 2 + 9)) = (m / (m ^ 2 + 9) + (2 * 3) / (m ^ 2 + 9)) := by 
      field_simp [(show m * m + 3 * 3 = m ^ 2 + 9 by ring)]
      <;> ring_nf
    rw [eq2]
    linarith [eq1]

  have h5 : m + 6 = 0 := by
    have h6 : m ^ 2 + 9 > 0 := h2
    have h7 : (m + 6) / (m ^ 2 + 9) = 0 := by
      linarith [hk3]
    have : m + 6 = 0 := by
      field_simp [(show m ^ 2 + 9 ≠ 0 by positivity)] at h7
      all_goals linarith
    assumption

  have hm : m = -6 := by linarith

  rw [hz1, hz2, hm]
  simp [Complex.abs, Complex.normSq]
  ring_nf
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  all_goals ring_nf <;> norm_num