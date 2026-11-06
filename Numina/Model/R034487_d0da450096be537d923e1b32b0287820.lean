import Mathlib

open Real Set
open scoped Real

theorem inequalities_86519 (θ : Real) (hθ : θ ∈ Ioo 0 (π/2)) :
    0 < sin θ + cos θ + tan θ + 1/tan θ - 1/cos θ - 1/sin θ ∧
    sin θ + cos θ + tan θ + 1/tan θ - 1/cos θ - 1/sin θ < 1 := by
  rcases hθ with ⟨h1, h2⟩
  have hsin : 0 < sin θ := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos, h1, h2]
    linarith [Real.pi_pos, h1, h2]
  have hcos : 0 < cos θ := by 
    apply cos_pos_of_mem_Ioo 
    constructor 
    all_goals linarith [Real.pi_pos, h1, h2]
  have hsinne : sin θ ≠ 0 := by linarith
  have hcosne : cos θ ≠ 0 := by linarith

  have htan : tan θ = sin θ / cos θ := by
    rw [tan_eq_sin_div_cos]

  constructor 
  · -- Show 0 < sin θ + cos θ + tan θ + 1/tan θ - 1/cos θ - 1/sin θ 
    have htan1 : 1 / tan θ = cos θ / sin θ := by 
      rw [htan]
      field_simp [hsinne, hcosne]

    rw [htan1, htan]

    have heq3 : sin θ + cos θ + (sin θ / cos θ) + (cos θ / sin θ) - (1 / cos θ) - (1 / sin θ) =
        ( sin θ ^ 2 * cos θ + cos θ ^ 2 * sin θ + sin θ ^ 2 + cos θ ^ 2 - sin θ - cos θ ) / ( sin θ * cos θ ) := by
      field_simp [hsinne, hcosne]
      ring

    rw [heq3]
    have hpos1 : sin θ * cos θ > 0 := by
      nlinarith [hsin, hcos]
    have hpos2 : sin θ ^ 2 * cos θ + cos θ ^ 2 * sin θ + sin θ ^ 2 + cos θ ^ 2 - sin θ - cos θ > 0 := by
      have hsin12 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
        apply Real.sin_sq_add_cos_sq θ
      nlinarith [sq_pos_of_pos hsin, sq_pos_of_pos hcos, mul_pos hsin hcos, sq_nonneg (sin θ ^ 2 - cos θ ^ 2), sq_nonneg (sin θ - cos θ), sq_nonneg (1 - (sin θ + cos θ)), Real.sin_sq_add_cos_sq θ, mul_pos hsin hcos]

    apply div_pos
    linarith
    all_goals nlinarith 
  · -- Show sin θ + cos θ + tan θ + 1/tan θ - 1/cos θ - 1/sin θ < 1
    have htan1 : 1 / tan θ = cos θ / sin θ := by 
      rw [htan]
      field_simp [hsinne, hcosne]

    rw [htan1, htan]

    have heq3 : sin θ + cos θ + (sin θ / cos θ) + (cos θ / sin θ) - (1 / cos θ) - (1 / sin θ) =
        ( sin θ ^ 2 * cos θ + cos θ ^ 2 * sin θ + sin θ ^ 2 + cos θ ^ 2 - sin θ - cos θ ) / ( sin θ * cos θ ) := by 
      field_simp [hsinne, hcosne]
      ring

    rw [heq3]
    have hpos1 : sin θ * cos θ > 0 := by
      nlinarith [hsin, hcos]
    have hpos2 : sin θ ^ 2 * cos θ + cos θ ^ 2 * sin θ + sin θ ^ 2 + cos θ ^ 2 - sin θ - cos θ < sin θ * cos θ := by 
      have hsin12 : sin θ ^ 2 + cos θ ^ 2 = 1 := by 
        apply Real.sin_sq_add_cos_sq θ
      nlinarith [sq_nonneg (sin θ - cos θ), sq_nonneg (sin θ - 1), sq_nonneg (cos θ - 1), sq_nonneg (sin θ ^ 2 - cos θ ^ 2), hsin, hcos, mul_pos hsin hcos]

    apply (div_lt_iff₀ (by nlinarith)).mpr 
    linarith