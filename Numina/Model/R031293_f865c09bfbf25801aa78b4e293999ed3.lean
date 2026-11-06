import Mathlib

open Real Set
open scoped Real

theorem algebra_15323 :
  IsLeast {x | ∃ θ : ℝ, θ ∈ Ioo 0 (π/2) ∧ x = 2 * cos θ + 1 / sin θ + sqrt 2 * tan θ} (3 * sqrt 2) := by
  constructor
  · -- Show that 3 * sqrt 2 is in the set
    use Real.pi / 4
    constructor
    · -- Show that π/4 is in the interval (0, π/2)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Compute the value at θ = π/4
      have h1 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      have h3 : tan (Real.pi / 4) = 1 := by
        rw [tan_eq_sin_div_cos]
        rw [h1, h2]
        field_simp
      rw [h1, h2, h3]
      field_simp
      <;> ring_nf <;> norm_num
  · -- Show that 3 * sqrt 2 is the minimum
    intro x hx
    rcases hx with ⟨θ, hθ, hx⟩
    rw [mem_Ioo] at hθ
    have h1 : 0 < θ := hθ.1
    have h2 : θ < Real.pi / 2 := hθ.2
    have h3 : 0 < sin θ := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h4 : 0 < cos θ := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    have htan : tan θ = sin θ / cos θ := by
      rw [tan_eq_sin_div_cos]
    rw [htan] at hx
    have h7 : 2 * cos θ + 1 / sin θ + Real.sqrt 2 * (sin θ / cos θ) ≥ 3 * Real.sqrt 2 := by
      have h8 : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      have h11 : 2 * cos θ + 1 / sin θ + Real.sqrt 2 * (sin θ / cos θ) - 3 * Real.sqrt 2 ≥ 0 := by
        have h12 : 2 * cos θ + 1 / sin θ + Real.sqrt 2 * (sin θ / cos θ) - 3 * Real.sqrt 2 =
            (2 * cos θ ^ 2 * sin θ + cos θ + Real.sqrt 2 * sin θ ^ 2 - 3 * Real.sqrt 2 * (sin θ * cos θ)) / (sin θ * cos θ) := by
          field_simp
          <;> ring
        rw [h12]
        have h13 : 0 < sin θ * cos θ := mul_pos h3 h4
        have h12' : 2 * cos θ ^ 2 * sin θ + cos θ + Real.sqrt 2 * sin θ ^ 2 - 3 * Real.sqrt 2 * (sin θ * cos θ) ≥ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0),
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ 2),
            sq_nonneg (sin θ - Real.sqrt 2 / 2), sq_nonneg (cos θ - Real.sqrt 2 / 2),
            sq_nonneg (sin θ ^ 2 - 1 / 2), sq_nonneg (cos θ ^ 2 - 1 / 2),
            sq_nonneg (sin θ - cos θ), sq_nonneg (sin θ * cos θ - 1 / 2),
            Real.sqrt_nonneg 2, sq_nonneg (2 * sin θ - Real.sqrt 2), sq_nonneg (2 * cos θ - Real.sqrt 2),
            Real.sqrt_nonneg 2, mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2),
            mul_pos h3 h4, h8, sq_nonneg (sin θ + cos θ - Real.sqrt 2)]
        apply div_nonneg
        linarith
        all_goals linarith
      linarith
    linarith [h7, hx]