import Mathlib

theorem algebra_247432 {z : ℂ} (hz : z ≠ 1) :
    (1 / (1 - z)).re = 2 ∧ (1 / (1 - z)).im = -1 ↔
    z = (3 / 5 - 1 / 5 * Complex.I) := by
  constructor
  · -- Forward direction: conditions imply z value
    intro h
    rcases h with ⟨h₁, h₂⟩
    have eq3 : (1 / (1 - z)).re = (1 - z.re) / ((1 - z.re)^2 + (z.im)^2) := by
      simp [Complex.div_re, Complex.normSq, Complex.re, Complex.im, sub_eq_zero, pow_two]
      <;> ring
    have eq4 : (1 / (1 -z)).im = (z.im) / ((1 - z.re)^2 + (z.im)^2) := by
      simp [Complex.div_im, Complex.normSq, Complex.re, Complex.im, sub_eq_zero, pow_two]
      <;> ring
    rw [eq3] at h₁ 
    rw [eq4] at h₂
    have h3 : (1 - z.re)^2 + (z.im)^2 ≠ 0 := by
      by_contra h
      have h4 : (1 - z.re)^2 = 0 := by
        nlinarith [sq_nonneg (1 - z.re), sq_nonneg z.im]
      have h5 : z.re = 1 := by
        nlinarith
      have h6 : z.im = 0 := by
        nlinarith [sq_nonneg (1 - z.re), sq_nonneg z.im]
      have h7 : z = 1 := by
        simp [Complex.ext_iff, h5, h6]
      contradiction
    have eq1' : (1 - z.re) = 2 * ((1 - z.re)^2 + (z.im)^2) := by
      have h4 : (1 - z.re)^2 + (z.im)^2 ≠ 0 := h3
      field_simp at h₁ ⊢
      nlinarith [h₁]
    have eq2' : z.im = -1 * ((1 - z.re)^2 + (z.im)^2) := by
      have h4 : (1 - z.re)^2 + (z.im)^2 ≠ 0 := h3
      field_simp at h₂ ⊢
      nlinarith [h₂]
    have eq3 : (1 - z.re)^2 + (z.im)^2 = -z.im := by
      nlinarith [eq2']
    have h5 : z.re = 1 + 2 * z.im := by
      nlinarith [eq1']
    have h6 : z.im * (5 * z.im + 1) = 0 := by
      nlinarith [eq3, h5]
    cases (mul_eq_zero.mp h6) with
    | inl h7 =>
      have h8 : z.re = 1 := by
        nlinarith [h5, h7]
      have h9 : z.im = 0 := by 
        linarith [h7]
      have h_eq_1 : z = 1 := by
        simp [Complex.ext_iff, h8, h9]
      contradiction
    | inr h8 =>
      have h7 : z.im = -1 / 5 := by 
        nlinarith [h8]
      have h8 : z.re = 3 / 5 := by
        nlinarith [h5, h7]
      rw [Complex.ext_iff] at *
      simp [h8, h7]
      all_goals norm_num
  · -- Reverse direction: z value implies conditions
    intro h
    rw [h]
    simp [Complex.div_re, Complex.div_im, Complex.normSq, Complex.re, Complex.im]
    all_goals norm_num