import Mathlib

open Real Set
open scoped Real

theorem algebra_118218 {α : ℝ} (hα : α ∈ Ioo (π/4) (π/2)) :
    (cos α)^(sin α) < (cos α)^(cos α) ∧ (cos α)^(cos α) < (sin α)^(cos α) := by
  rcases hα with ⟨h1, h2⟩
  have h3 : 0 < π := Real.pi_pos
  have h4 : π / 4 < π / 2 := by linarith [Real.pi_pos]
  -- cos(α) < sin(α)
  have h7 : cos α < sin α := by
    have h17 : cos α < cos (π / 4) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [h1, h2, Real.pi_pos]
    have h18 : sin (π / 4) < sin α := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [h1, h2, Real.pi_pos]
    have h19 : cos (π / 4) = sin (π / 4) := by
      have h19 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      have h20 : sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      linarith [h19, h20]
    have h20 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    have h21 : sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    linarith [h17, h18, h19, h20, h21]
  have h9 : cos α < 1 := by
    have h10 : cos α < cos (0 : ℝ) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [h1, h2, Real.pi_pos]
    have h11 : cos (0 : ℝ) = 1 := Real.cos_zero
    linarith [h10, h11]
  have h10 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [h1, h2, Real.pi_pos]
  have h14 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [h1, h2, Real.pi_pos]
  constructor
  · -- Prove that $(\cos \alpha)^{\sin \alpha} < (\cos \alpha)^{\cos \alpha}$
    have h8 : (cos α)^(sin α) < (cos α)^(cos α) := by
      -- cos(α) in (0, 1)
      -- sin(α) > cos(α)
      -- The function f(x) = cos(α)^x is strictly decreasing
      -- since 0 < cos(α) < 1
      have h9 : cos α < 1 := by
        linarith [show cos α < cos (0 : ℝ) by apply Real.cos_lt_cos_of_nonneg_of_le_pi; all_goals linarith [h1, h2, Real.pi_pos], Real.cos_zero]
      have h11 : sin α > cos α := h7
      have h12 : (cos α) ^ (sin α) < (cos α) ^ (cos α) := by
        apply Real.rpow_lt_rpow_of_exponent_gt
        all_goals linarith [h9, h10, h11]
      exact h12
    exact h8
  · -- Prove that $(\cos \alpha)^{\cos \alpha} < (\sin \alpha)^{\cos \alpha}$
    -- Using that cos(α) < sin(α) and cos(α) > 0
    have h13 : (cos α)^(cos α) < (sin α)^(cos α) := by
      -- We can use the fact that cos α < sin α and rpow is strictly increasing
      -- when the base is greater than 1.
      -- But sin α^cos α > cos α^cos α because sin α > cos α
      have h14 : cos α > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor <;> linarith [h1, h2, Real.pi_pos]
      have h15 : sin α > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        all_goals linarith [h1, h2, Real.pi_pos]
      have h16 : cos α < sin α := h7
      -- Using strictly increasing of rpow
      have h18 : (cos α) ^ (cos α) < (sin α) ^ (cos α) := by
        apply Real.rpow_lt_rpow
        all_goals
          try linarith [h14, h15, h16]
          all_goals try nlinarith
      exact h18
    exact h13