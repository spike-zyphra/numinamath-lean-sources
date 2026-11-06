import Mathlib

open Real Set
open scoped Real

theorem algebra_10453 (θ : ℝ) (hθ : θ ∈ Ioo 0 (π/2)) :
  IsGreatest {x | ∃ θ : ℝ, θ ∈ Ioo 0 (π/2) ∧ x = 2 * sin θ * cos θ / ((sin θ + 1) * (cos θ + 1))} (6 - 4 * sqrt 2) := by
  constructor
  · -- Show that 6 - 4 * sqrt 2 is in the set.
    use (Real.pi / 4)
    constructor
    · -- Show that π / 4 is in the open interval (0, π / 2)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show that at θ = π / 4, the expression equals 6 - 4 * sqrt 2
      have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [sin_pi_div_four]
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      rw [h1, h2]
      field_simp
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_pos_of_pos (show (0 : ℝ) < Real.sqrt 2 by positivity), sq_nonneg (Real.sqrt 2 ^ 2 - 2), mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)) (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num))]
  · -- Show that 6 - 4 * sqrt 2 is indeed the greatest.
    intro x hx
    rcases hx with ⟨θ, hθ, hx_eq⟩
    rcases hθ with ⟨h1, h2⟩
    have h3 : 0 < sin θ := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [h1, Real.pi_pos]
      linarith [h2, Real.pi_pos]
    have h4 : 0 < cos θ := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [h1, Real.pi_pos]
      · linarith [h2, Real.pi_pos]
    have h5 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq θ
    have h6 : 2 * sin θ * cos θ / ((sin θ + 1) * (cos θ + 1)) ≤ 6 - 4 * Real.sqrt 2 := by
      have h6' : 0 < (sin θ + 1) * (cos θ + 1) := by
        have h7 : sin θ + 1 > 0 := by
          linarith [h3]
        have h8 : cos θ + 1 > 0 := by
          linarith [h4]
        nlinarith
      have h7 : 2 * sin θ * cos θ ≤ (6 - 4 * Real.sqrt 2) * ((sin θ + 1) * (cos θ + 1)) := by
        nlinarith [sq_nonneg (sin θ - cos θ), sq_nonneg (sin θ + cos θ - 1), sq_nonneg (sin θ + cos θ - Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sin θ ^ 2 - cos θ ^ 2), mul_pos h3 h4, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), sq_nonneg (sin θ - Real.sqrt 2 / 2), sq_nonneg (cos θ - Real.sqrt 2 / 2)]
      have h9 : 0 < (sin θ + 1) * (cos θ + 1) := h6'
      apply (div_le_iff₀ h9).mpr
      nlinarith
    have h_eq : x = 2 * sin θ * cos θ / ((sin θ + 1) * (cos θ + 1)) := by
      linarith [hx_eq]
    linarith [h_eq, h6]