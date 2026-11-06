import Mathlib

theorem algebra_157995 (f : ℝ → ℝ) (hf : f = fun x => 2 * (Real.cos x)^2 + 1) :
    IsLeast {x | 0 < x ∧ f = fun y => f (y + x)} (Real.pi) := by 
  constructor
  · -- Show that π is in the set
    constructor
    · -- Show π > 0
      positivity
    · -- Show that f = fun y => f (y + Real.pi)
      funext y
      rw [hf]
      have h : 2 * Real.cos y ^ 2 + 1 = 2 * Real.cos (y + Real.pi) ^ 2 + 1 := by
        have hcos : Real.cos (y + Real.pi) = -Real.cos y := Real.cos_add_pi y
        rw [hcos]
        all_goals nlinarith 
      simpa using h 
  · -- Show minimality of π
    intro T ⟨hTpos, hTeq⟩
    by_contra h'
    push_neg at h'
    have eq4 : f (Real.pi / 2) = f (Real.pi / 2 + T) := by 
      have eq4' := congr_arg (fun x => x (Real.pi / 2)) hTeq
      simpa using eq4'
    -- Compute both sides
    have eq5 : f (Real.pi / 2) = 1 := by
      rw [hf]
      simp [Real.cos_pi_div_two]
      all_goals nlinarith
    have eq6 : f (Real.pi / 2 + T) = 2 * Real.sin T ^ 2 + 1 := by 
      rw [hf]
      have h7 : Real.cos (Real.pi / 2 + T) = - Real.sin T := by
        rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
        all_goals ring
      simp [h7]
      all_goals nlinarith
    rw [eq5] at eq4
    rw [eq6] at eq4
    have h3 : Real.sin T > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      linarith [hTpos, Real.pi_gt_three]
      nlinarith [hTpos, show T < Real.pi by linarith [h', Real.pi_pos], Real.pi_gt_three]
    have h8 : Real.sin T = 0 := by 
      nlinarith
    linarith