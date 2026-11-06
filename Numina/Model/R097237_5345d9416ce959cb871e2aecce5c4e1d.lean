import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9446 {f : ℝ → ℝ} (hf : f = λ x => sin (2 * x) * cos (2 * x)) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi / 2) := by 
  constructor
  · -- First, we verify π/2 is a positive period of f
    constructor
    · -- Show π/2 > 0
      positivity
    · -- Show f = fun x ↦ f (x + π / 2)
      rw [hf]
      funext x
      have eq1 : sin (2 * x) * cos (2 * x) = sin (2 * (x + Real.pi / 2)) * cos (2 * (x + Real.pi / 2)) := by
        have h1 : 2 * (x + Real.pi / 2) = 2 * x + Real.pi := by ring
        rw [h1]
        have h2 : sin (2 * x + Real.pi) = - sin (2 * x) := by
          rw [sin_add_pi]
        have h3 : cos (2 * x + Real.pi) = - cos (2 * x) := by
          rw [cos_add_pi]
        rw [h2, h3]
        ring
      simp [eq1]
  · -- Next, we need to prove that π/2 is the smallest positive period
    intro T ⟨hT_pos, hT_period⟩
    by_contra h
    push_neg at h
    have h' := congr_arg (λ g => g (Real.pi / 4 - T / 2)) hT_period
    simp [hf] at h'
    have h1 : 0 < T := hT_pos
    have h2 : Real.sin T > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals nlinarith [Real.pi_gt_three, Real.pi_pos, h1, h]
    have h3 : Real.cos T > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      nlinarith [Real.pi_pos, Real.pi_gt_three, h1, h]
      nlinarith [Real.pi_pos, Real.pi_gt_three, h1, h]
    -- Now we will compute both sides of the equation to derive a contradiction
    have eq1 : sin (2 * (Real.pi / 4 - T / 2)) * cos (2 * (Real.pi / 4 - T / 2)) = 
        sin (2 * (Real.pi / 4 - T / 2 + T)) * cos (2 * (Real.pi / 4 - T / 2 + T)) := by 
        linarith [h']
    have eq2 : sin (2 * (Real.pi / 4 - T / 2 + T)) * cos (2 * (Real.pi / 4 - T / 2 + T)) = - sin T * cos T := by
      have h4 : 2 * (Real.pi / 4 - T / 2 + T) = Real.pi / 2 + T := by ring
      rw [h4]
      have h5 : sin (Real.pi / 2 + T) = cos T := by 
        rw [sin_add]
        simp [sin_pi_div_two, cos_pi_div_two]
        all_goals linarith
      have h6 : cos (Real.pi / 2 + T) = - sin T := by 
        rw [cos_add]
        simp [sin_pi_div_two, cos_pi_div_two]
        all_goals linarith
      rw [h5, h6]
      all_goals linarith
    have eq3 : sin (2 * (Real.pi / 4 - T / 2)) * cos (2 * (Real.pi / 4 - T / 2)) = 
        sin T * cos T := by 
      have h7 : 2 * (Real.pi / 4 - T / 2) = Real.pi / 2 - T := by ring
      rw [h7]
      have h8 : sin (Real.pi / 2 - T) = cos T := by 
        rw [sin_sub]
        simp [sin_pi_div_two, cos_pi_div_two]
        all_goals linarith
      have h9 : cos (Real.pi / 2 - T) = sin T := by 
        rw [cos_sub]
        simp [sin_pi_div_two, cos_pi_div_two]
        all_goals linarith
      rw [h8, h9]
      all_goals linarith
    rw [eq3] at eq1
    rw [eq2] at eq1
    nlinarith [h2, h3]