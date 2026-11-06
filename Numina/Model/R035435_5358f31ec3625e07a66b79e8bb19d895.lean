import Mathlib

open Real Set
open scoped Real

theorem algebra_130852 (α β : Real) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : sin α = cos (α + β) * sin β) :
    tan α ≤ sqrt 2 / 4 := by
  rcases h₀ with ⟨h₀1, h₀2⟩
  rcases h₁ with ⟨h₁1, h₁2⟩
  have hα1 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₀1, Real.pi_pos]
    linarith [h₀2, Real.pi_pos]
  have hα2 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [h₀1, h₀2, Real.pi_pos]
  have h3 : cos (α + β) = cos α * cos β - sin α * sin β := by
    rw [cos_add]
  rw [h3] at h₂
  have h4 : sin α * (1 + sin β ^ 2) = cos α * (cos β * sin β) := by
    nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
  have h5 : tan α = (cos β * sin β) / (1 + sin β ^ 2) := by
    have htan : tan α = sin α / cos α := by
      rw [tan_eq_sin_div_cos]
    rw [htan]
    have h4' : sin α * (1 + sin β ^ 2) = cos α * (cos β * sin β) := h4
    have hcos : cos α > 0 := hα2
    field_simp [hcos, show 1 + sin β ^ 2 > 0 by nlinarith [h₁1, sq_nonneg (sin β), sq_nonneg (cos β), Real.sin_sq_add_cos_sq β]]
    <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
  have h7 : 0 < sin β := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₁1, Real.pi_pos]
    linarith [h₁2, Real.pi_pos]
  have h8 : 0 < cos β := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [h₁1, h₁2, Real.pi_pos]
  have h9 : 1 + sin β ^ 2 > 0 := by
    nlinarith [h7, sq_nonneg (sin β), sq_nonneg (cos β), Real.sin_sq_add_cos_sq β]
  have h11 : (cos β * sin β) / (1 + sin β ^ 2) ≤ sqrt 2 / 4 := by
    have h18 : sin β ^ 2 + cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
    have h19 : 0 < (1 + sin β ^ 2 : ℝ) := by
      nlinarith [h7, sq_nonneg (sin β), sq_nonneg (cos β), Real.sin_sq_add_cos_sq β]
    have h17 : cos β * sin β ≤ (sqrt 2 / 4) * (1 + sin β ^ 2) := by
      have h6 : (cos β * sin β) ^ 2 ≤ ((sqrt 2 / 4) ^ 2) * (1 + sin β ^ 2) ^ 2 := by
        have h18' : sin β ^ 2 + cos β ^ 2 = 1 := h18
        have h21 : (cos β * sin β) ^ 2 = cos β^2 * sin β^2 := by ring
        rw [h21] at *
        nlinarith [sq_nonneg (sin β ^ 2 - 1 / 3), sq_nonneg (cos β ^ 2 - 1 / 3), sq_nonneg (sin β ^ 2 - cos β ^ 2), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by linarith), sq_nonneg (cos β * sin β), h18']
      have h7_pos : cos β * sin β ≥ 0 := by nlinarith
      have h8_pos : (sqrt 2 / 4) * (1 + sin β ^ 2) ≥ 0 := by
        have h2sin : sin β ^ 2 ≥ 0 := sq_nonneg (sin β)
        have hsqrt2 : sqrt (2 : ℝ) > 0 := Real.sqrt_pos.mpr (by linarith : (2 : ℝ) > 0)
        nlinarith
      have h9 : cos β * sin β ≤ (sqrt 2 / 4) * (1 + sin β ^ 2) := by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), h6, sq_nonneg ((cos β * sin β) - (sqrt 2 / 4) * (1 + sin β ^ 2)), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by linarith)]
      linarith
    apply (div_le_iff₀ h19).mpr
    linarith [h17]
  linarith [h5, h11]