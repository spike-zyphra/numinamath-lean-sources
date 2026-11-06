import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Real

theorem sin_3α_bounds (α : ℝ) (hα : 0 < α ∧ α < π/6) :
    2 * sin α < sin (3 * α) ∧ sin (3 * α) < 3 * sin α := by
  rcases hα with ⟨h1, h2⟩
  have h3 : 0 < α := h1
  have h4 : α < π / 6 := h2

  have h5 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h3, h4, Real.pi_pos]
    linarith [h3, h4, Real.pi_pos]

  have h6 : sin α < 1 / 2 := by
    have h7 : sin α < sin (π / 6) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [h3, h4, Real.pi_pos]
    have h8 : sin (π / 6) = 1 / 2 := sin_pi_div_six
    linarith [h7, h8]

  have h8 : sin (3 * α) = 3 * sin α - 4 * sin α ^ 3 := by
    rw [sin_three_mul]

  have h9 : 2 * sin α < sin (3 * α) := by
    rw [h8]
    have h10 : sin α * (1 - 4 * sin α ^ 2) > 0 := by
      have h11 : sin α > 0 := h5
      have h12 : sin α ^ 2 < (1 / 4 : ℝ) := by
        nlinarith [h6, sq_pos_of_pos h5]
      have h13 : 1 - 4 * sin α ^ 2 > 0 := by
        nlinarith
      nlinarith
    nlinarith
  have h10 : sin (3 * α) < 3 * sin α := by
    rw [h8]
    have h11 : 4 * sin α ^ 3 > 0 := by
      have h4_pos : sin α ^ 3 > 0 := by
        have h5_pos : sin α > 0 := h5
        positivity
      nlinarith
    nlinarith [sq_pos_of_pos h5, sq_pos_of_pos h5, sq_nonneg (sin α ^ 2)]

  constructor
  · -- First inequality: 2 * sin α < sin (3 * α)
    linarith [h9]
  · -- Second inequality: sin (3 * α) < 3 * sin α
    linarith [h10]