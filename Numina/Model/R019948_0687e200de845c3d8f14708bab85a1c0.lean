import Mathlib

open Real Set
open scoped Real

theorem inequalities_299771 (m : ℝ) :
  (∀ θ ∈ Icc 0 (π/2), (cos θ)^2 + 2 * m * sin θ - 2 * m - 2 < 0) ↔ m > -1/2 := by
  constructor
  · -- Forward: if ∀ θ ∈ Icc 0 (π / 2), (cos θ)^2 + 2 * m * sin θ - 2 * m - 2 < 0 then m > -1 / 2
    intro h
    have h1 := h 0 (by
      constructor <;> linarith [Real.pi_pos]
    )
    simp [Real.sin_zero, Real.cos_zero] at h1
    linarith
  · -- Backward: m > -1/2 then ∀ θ ∈ Icc 0 (π / 2), (cos θ)^2 + 2 * m * sin θ - 2 * m - 2 < 0
    intro hm θ hθ
    rcases hθ with ⟨hθ1, hθ2⟩
    have h1 : 0 ≤ θ := by linarith
    have h2 : θ ≤ π / 2 := by linarith
    have h3 : sin θ ≥ 0 := by
      apply sin_nonneg_of_nonneg_of_le_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h4 : cos θ ≥ 0 := by
      apply cos_nonneg_of_mem_Icc
      constructor <;> linarith [Real.pi_pos]
    -- Derive bounds for sin θ and cos θ
    have h5 : sin θ ≤ 1 := by 
      have h5 : sin θ ≤ sin (Real.pi / 2) := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        all_goals linarith [Real.pi_pos]
      have h5' : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      linarith
    have h6 : cos θ ≤ 1 := by 
      have h6 : cos θ ≤ cos (0 : ℝ) := by
        apply Real.cos_le_cos_of_nonneg_of_le_pi
        all_goals linarith [Real.pi_pos]
      have h6' : cos (0 : ℝ) = 1 := Real.cos_zero
      linarith
    have h7 : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    have h8 : cos θ ^ 2 = 1 - sin θ ^ 2 := by
      linarith
    nlinarith [sq_nonneg (sin θ - 1), sq_nonneg (m - (-1 / 2)), sq_nonneg (sin θ - m), Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq θ, mul_nonneg (show 0 ≤ sin θ by linarith) (show 0 ≤ cos θ by linarith), Real.sin_sq_add_cos_sq θ, hm]