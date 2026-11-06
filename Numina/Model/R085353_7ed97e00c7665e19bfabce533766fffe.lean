import Mathlib

open Real Set
open scoped Real

theorem algebra_196729 :
  IsLeast {x : ℝ | ∃ α : ℝ, α ∈ Icc 0 (π/2) ∧ x = sin α ^ 4 + cos α ^ 4} (1/2) := by
  constructor
  · use Real.pi / 4
    constructor
    · -- Show that π/4 ∈ [0, π/2]
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Calculate that sin(π/4)^4 + cos(π/4)^4 = 1/2
      have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [sin_pi_div_four]
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      rw [h1, h2]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
  · -- Show that 1/2 is the least element in the set
    rintro x ⟨α, ⟨hα₁, hα₂⟩, hx⟩
    have h1 : sin α ^ 4 + cos α ^ 4 ≥ 1 / 2 := by
      have h2 : sin α ^ 2 + cos α ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq α
      have h3 : sin α ^ 4 + cos α ^ 4 = 1 - 2 * (sin α ^ 2 * cos α ^ 2) := by
        calc
          sin α ^ 4 + cos α ^ 4 = (sin α ^ 2 + cos α ^ 2)^2 - 2 * (sin α ^ 2 * cos α ^ 2) := by
            nlinarith [h2]
          _ = (1)^2 - 2 * (sin α ^ 2 * cos α ^ 2) := by rw [h2]
          _ = 1 - 2 * (sin α ^ 2 * cos α ^ 2) := by ring
      have h4 : sin α ^ 2 * cos α ^ 2 ≤ 1 / 4 := by
        nlinarith [sq_nonneg (sin α ^ 2 - cos α ^ 2), Real.sin_sq_add_cos_sq α, sq_nonneg (sin α * cos α), sq_nonneg (sin α ^ 2 - 1 / 2), sq_nonneg (cos α ^ 2 - 1 / 2), Real.sin_sq_add_cos_sq α]
      rw [h3]
      nlinarith
    linarith [hx, h1]