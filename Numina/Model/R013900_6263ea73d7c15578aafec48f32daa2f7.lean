import Mathlib

theorem algebra_99934 {f : ℝ → ℝ} (hf : ∀ x, f x = 3 * Real.sin x + 2 * Real.cos x + 1)
    (a b c : ℝ) (ha : ∀ x, a * f x + b * f (x - c) = 1) :
    b * Real.cos c / a = -1 := by
  have h1 := ha 0
  simp [hf, Real.sin_zero, Real.cos_zero] at h1
  have h2 := ha (Real.pi / 2)
  simp [hf, Real.sin_pi_div_two, Real.cos_pi_div_two] at h2
  have h3 := ha c
  simp [hf, Real.sin_zero, Real.cos_zero] at h3
  have h4 := ha (Real.pi / 2 + c)
  simp [hf, Real.sin_add, Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two] at h4
  have h5 := ha (Real.pi)
  simp [hf, Real.sin_pi, Real.cos_pi] at h5
  have h6 := ha (Real.pi + c)
  simp [hf, Real.sin_add, Real.cos_add, Real.sin_pi, Real.cos_pi] at h6
  have h7 : a ≠ 0 := by
    by_contra ha0
    rw [ha0] at ha
    have h1' := ha 0
    simp [hf, Real.sin_zero, Real.cos_zero] at h1'
    have h2' := ha (Real.pi / 2)
    simp [hf, Real.sin_pi_div_two, Real.cos_pi_div_two] at h2'
    have h3' := ha (c)
    simp [hf, Real.sin_zero, Real.cos_zero] at h3'
    have h4' := ha (Real.pi / 2 + c)
    simp [hf, Real.sin_add, Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two] at h4'
    have h5' := ha (Real.pi)
    simp [hf, Real.sin_pi, Real.cos_pi] at h5'
    have h6' := ha (Real.pi + c)
    simp [hf, Real.sin_add, Real.cos_add, Real.sin_pi, Real.cos_pi] at h6'
    linarith
  have h8 : b * Real.cos c = -a := by
    have eq1 : a * (3 * Real.sin c + 2 * Real.cos c + 1) + b * 3 = 1 := by
      have h3 := ha c
      simp [hf, Real.sin_zero, Real.cos_zero] at h3
      linarith
    have eq2 : 3 * a + b * (-3 * Real.sin c + 2 * Real.cos c + 1) = 1 := by
      have h1 := ha 0
      simp [hf, Real.sin_zero, Real.cos_zero] at h1 
      linarith
    -- have eq3 : a * (3 * Real.cos c - 2 * Real.sin c + 1) + b * 4 = 1 := by
    --  have h4 := ha (Real.pi / 2 + c)
    --  simp [hf, Real.sin_add, Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two] at h4
    --  linarith
    -- have eq4 : 4 * a + b * (3 * Real.cos c + 1) = 1 := by
    --  have h2 := ha (Real.pi / 2)
    --  simp [hf, Real.sin_pi_div_two, Real.cos_pi_div_two] at h2
    --  linarith
    nlinarith [Real.sin_sq_add_cos_sq c, sq_nonneg (Real.sin c), sq_nonneg (Real.cos c), sq_pos_of_ne_zero (show a ≠ 0 by assumption), sq_nonneg (a), sq_nonneg (b), sq_nonneg (a + b - 1)]
  have : b * Real.cos c / a = -1 := by
    have h9 : b * Real.cos c = -a := h8
    have h10 : a ≠ 0 := h7
    field_simp [h10]
    linarith
  assumption