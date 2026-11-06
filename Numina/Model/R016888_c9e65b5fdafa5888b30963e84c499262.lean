import Mathlib

open Real Set
open scoped Real

theorem algebra_307656 (φ : ℝ) (hφ : π/4 < φ ∧ φ < π/2) (h : sin φ * cos φ = 60/169) :
    sin φ = 12/13 ∧ cos φ = 5/13 := by

  rcases hφ with ⟨h1, h2⟩
  have h3 : sin φ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    . linarith [h1, h2, Real.pi_pos]
    . linarith [h1, h2, Real.pi_pos]

  have h4 : cos φ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [h1, h2, Real.pi_pos]

  have h5 : sin φ ^ 2 + cos φ ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq φ

  have h6 : (sin φ + cos φ) ^ 2 = 289 / 169 := by
    nlinarith

  have h7 : sin φ + cos φ = 17 / 13 := by
    have h8 : sin φ + cos φ > 0 := by
      nlinarith [h3, h4]
    nlinarith [h6, h8]

  have h8 : sin φ > cos φ := by
    have h9 : sin φ > Real.sqrt 2 / 2 := by
      have h10 : φ > Real.pi / 4 := h1
      have h11 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        rw [Real.sin_pi_div_four]
      have h12 : Real.sin (Real.pi / 4) < Real.sin φ := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [h1, h2, Real.pi_pos]
      nlinarith [h11, h12]
    have h13 : cos φ < Real.sqrt 2 / 2 := by 
      have h14 : φ > Real.pi / 4 := h1
      have h15 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [Real.cos_pi_div_four]
      have h16 : Real.cos φ < Real.cos (Real.pi / 4) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals linarith [h1, h2, Real.pi_pos]
      nlinarith [h15, h16]
    nlinarith [h9, h13]

  have h9 : sin φ = 12 / 13 := by 
    have h10 : cos φ = 17 / 13 - sin φ := by 
      linarith [h7]
    rw [h10] at h
    have h100 : (sin φ - 12 / 13) * (sin φ - 5 / 13) = 0 := by
      nlinarith [h]
    cases' (mul_eq_zero.mp h100) with h11 h111
    · -- sin φ = 12/13
      linarith
    · -- sin φ = 5/13
      nlinarith [h8, h111]

  have h10 : cos φ = 5 / 13 := by 
    nlinarith [h7, h9]

  exact ⟨h9, h10⟩