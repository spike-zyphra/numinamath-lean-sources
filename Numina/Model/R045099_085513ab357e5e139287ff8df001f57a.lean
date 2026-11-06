import Mathlib

open Real

theorem inequalities_610036 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < sin θ + cos θ + tan θ + cot θ - 1 / cos θ - 1 / sin θ ∧
    sin θ + cos θ + tan θ + cot θ - 1 / cos θ - 1 / sin θ < 1 := by
  rcases hθ with ⟨h1, h2⟩
  have h3 : sin θ > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [h1, h2, Real.pi_pos]
  have h4 : cos θ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [h1, h2, Real.pi_pos]
  have h5 : sin θ * cos θ > 0 := mul_pos h3 h4
  have h6 : sin θ + cos θ - 1 > 0 := by 
    nlinarith [sq_pos_of_pos h3, sq_pos_of_pos h4, Real.sin_sq_add_cos_sq θ, mul_pos h3 h4]

  have htan : tan θ = sin θ / cos θ := by 
    rw [tan_eq_sin_div_cos]

  have hcot : cot θ = cos θ / sin θ := by 
    rw [cot_eq_cos_div_sin]

  -- rewrite all terms into one expression divided by sin θ * cos θ
  have h11 : sin θ + cos θ + tan θ + cot θ - 1 / cos θ - 1 / sin θ =
      (sin θ^2 * cos θ + sin θ * cos θ^2 + sin θ^2 + cos θ^2 - sin θ - cos θ) / (sin θ * cos θ) := by
    rw [htan, hcot]
    field_simp [h3.ne', h4.ne']
    <;> ring_nf
  
  rw [h11]
  
  constructor
  · -- Prove that the expression is greater than 0
    apply div_pos
    · -- Show that the numerator is positive
      have h13 : sin θ^2 + cos θ^2 = 1 := Real.sin_sq_add_cos_sq θ
      nlinarith [sq_pos_of_pos h3, sq_pos_of_pos h4, sq_nonneg (sin θ - cos θ), sq_nonneg (sin θ + cos θ - 1), h13, mul_pos h3 h4]

    · -- Show that the denominator is positive
      positivity

  · -- Prove that the expression is less than 1
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [sq_pos_of_pos h3, sq_pos_of_pos h4, sq_nonneg (sin θ - cos θ), sq_nonneg (sin θ + cos θ - 1), 
      Real.sin_sq_add_cos_sq θ, mul_pos h3 h4]