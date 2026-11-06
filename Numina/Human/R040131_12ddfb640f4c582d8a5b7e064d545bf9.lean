import Mathlib

open Real Set
open scoped Real
/-when 0<θ<π, the maximum value of the function y=(1/sin θ - 1) * (1/cos θ - 1) is ?-/
theorem algebra_158124 (θ : ℝ) (hθ : θ ∈ Ioo 0 (π/2)) :
    (1/sin θ - 1) * (1/cos θ - 1) ≤ 3 - 2*sqrt 2 := by
  have h1 : 0 < θ := hθ.left
  have h2 : θ < π / 2 := hθ.right
  have h3 : sin θ > 0 := by
    apply sin_pos_of_mem_Ioo
    constructor
    · linarith [h1, Real.pi_pos]
    · linarith [h2, Real.pi_pos]
  have h4 : cos θ > 0 := by
    have h5 : θ < π / 2 := h2
    have h6 : cos θ > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [h1, Real.pi_pos]
      · linarith [h5, Real.pi_pos]
    exact h6
  have h5 : (1 / sin θ - 1) * (1 / cos θ - 1) ≤ 3 - 2 * sqrt 2 := by
    have h6 : 0 < sin θ := h3
    have h7 : 0 < cos θ := h4
    have h8 : (1 / sin θ - 1) * (1 / cos θ - 1) = (sin θ + cos θ - 1) / (sin θ + cos θ + 1) := by
      field_simp [h6.ne.symm, h7.ne.symm]
      nlinarith [Real.sin_sq_add_cos_sq θ, mul_pos h6 h7]
    rw [h8]
    have h9 : sin θ + cos θ ≤ Real.sqrt 2 := by
      have h10 : (sin θ + cos θ) ^ 2 ≤ 2 := by
        have h11 : (sin θ + cos θ) ^ 2 = sin θ ^ 2 + cos θ ^ 2 + 2 * sin θ * cos θ := by ring
        rw [h11]
        have h12 : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
        have h13 : 2 * sin θ * cos θ ≤ 1 := by
          have h14 : sin (2 * θ) = 2 * sin θ * cos θ := Real.sin_two_mul θ
          have h15 : sin (2 * θ) ≤ 1 := Real.sin_le_one (2 * θ)
          linarith
        nlinarith
      have h16 : sin θ + cos θ ≥ 0 := by nlinarith [h6, h7]
      apply Real.le_sqrt_of_sq_le
      nlinarith
    have h10 : (sin θ + cos θ - 1) / (sin θ + cos θ + 1) ≤ 3 - 2 * sqrt 2 := by
      have h11 : sin θ + cos θ ≤ Real.sqrt 2 := h9
      have h12 : sin θ + cos θ + 1 > 0 := by nlinarith [h6, h7, Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num : (0:ℝ) < 2)]
      have h13 : (sin θ + cos θ - 1) / (sin θ + cos θ + 1) - (3 - 2 * sqrt 2) ≤ 0 := by
        have h14 : (sin θ + cos θ - 1) / (sin θ + cos θ + 1) - (3 - 2 * sqrt 2) = 
          (sin θ + cos θ - 1 - (3 - 2 * sqrt 2) * (sin θ + cos θ + 1)) / (sin θ + cos θ + 1) := by 
          field_simp
          ring
        rw [h14]
        have h15 : sin θ + cos θ - 1 - (3 - 2 * sqrt 2) * (sin θ + cos θ + 1) ≤ 0 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2), h3, h4, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), h9, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_self_nonneg (sin θ - cos θ), Real.sin_sq_le_one θ, Real.cos_sq_le_one θ]
        apply div_nonpos_of_nonpos_of_nonneg
        · linarith
        · nlinarith [h12]
      linarith
    linarith
  linarith