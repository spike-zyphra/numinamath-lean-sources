import Mathlib

theorem algebra_242708 (d : ℝ) (h₀ : d > 0) :
    (d / 80) + (d / 80) < (d / 90) + (d / 70) := by
  have h1 : (d / 80) + (d / 80) = d / 40 := by
    ring_nf
  have h2 : (d / 90) + (d / 70) = 8 * d / 315 := by
    field_simp
    ring
  rw [h1, h2]
  have h4 : d / 40 < 8 * d / 315 := by
    have h3 : 0 < d := h₀
    have h5 : d / 40 - 8 * d / 315 < 0 := by
      have h6 : d / 40 - 8 * d / 315 = (-5 * d) / 12600 := by
        field_simp
        ring
      rw [h6]
      have h7 : -5 * d < (0 : ℝ) := by
        nlinarith
      have h8 : (0 : ℝ) < (12600 : ℝ) := by norm_num
      have h9 : (-5 * d) / (12600 : ℝ) < (0 : ℝ) := by
        apply (div_lt_iff₀ (by linarith)).mpr
        linarith
      linarith
    linarith
  linarith