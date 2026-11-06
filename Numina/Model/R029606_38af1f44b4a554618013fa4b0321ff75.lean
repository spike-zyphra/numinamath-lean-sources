import Mathlib

open Real


theorem algebra_9453 {f : ℝ → ℝ} (hf : f = fun x => Real.cos (2 * x)) :
    IsLeast {T | 0 < T ∧ f = fun x => f (x + T)} (Real.pi) := by
  constructor
  · -- Show pi is in the set
    constructor 
    · -- Show 0 < pi
      positivity
    · -- Show f = fun x => f (x + Real.pi)
      funext x
      simp only [hf]
      have h1 : Real.cos (2 * (x + Real.pi)) = Real.cos (2 * x) := by
        have h2 : 2 * (x + Real.pi) = 2 * x + 2 * Real.pi := by ring 
        rw [h2]
        have h3 : Real.cos (2 * x + 2 * Real.pi) = Real.cos (2 * x) := by 
          rw [show 2 * x + 2 * Real.pi = (2 * x) + 2 * Real.pi by ring]
          rw [Real.cos_add]
          simp [Real.cos_two_pi, Real.sin_two_pi]
        linarith
      simp [h1]
  · -- Show pi is the smallest
    intro T ⟨htpos, htperiod⟩
    by_contra h 
    push_neg at h 
    have h1 : f = fun x => f (x + T) := htperiod 
    have h1' : ∀ x, f x = f (x + T) := by 
      intro x 
      simpa using congr_fun h1 x 
    have eq1 := h1' 0 
    have eq2 := h1' (Real.pi / 4)
    simp only [hf] at eq1 eq2 
    have eq3 : 1 = Real.cos (2 * T) := by 
      have h21 : Real.cos (2 * 0) = 1 := by 
        simp [Real.cos_zero] 
      have eq4 : Real.cos (2 * 0) = Real.cos (2 * T) := by 
        simpa using eq1 
      linarith 
    have eq4 : 0 = - Real.sin (2 * T) := by 
      have h22 : Real.cos (2 * (Real.pi / 4)) = 0 := by 
        have h23 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring 
        rw [h23] 
        norm_num 
      have h24 : Real.cos (2 * (Real.pi / 4 + T)) = - Real.sin (2 * T) := by 
        have h25 : 2 * (Real.pi / 4 + T) = Real.pi / 2 + 2 * T := by ring 
        rw [h25] 
        have h26 : Real.cos (Real.pi / 2 + 2 * T) = - Real.sin (2 * T) := by 
          rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two] 
          all_goals ring 
        rw [h26] 
      have eq2' : Real.cos (2 * (Real.pi / 4)) = Real.cos (2 * (Real.pi / 4 + T)) := by 
        simpa using eq2 
      rw [h22, h24] at eq2' 
      linarith 
    have eq5 : Real.sin (2 * T) = 0 := by linarith 
    have eq6 : Real.cos (2 * T) = 1 := by linarith
    have eq7 : ∃ k : ℤ, 2 * T = k * (2 * Real.pi) := by 
      rw [Real.cos_eq_one_iff] at eq6 
      rcases eq6 with ⟨k, hk⟩ 
      refine' ⟨k, by nlinarith⟩ 
    rcases eq7 with ⟨k, hk⟩
    have h29 : T = (k : ℝ) * Real.pi := by 
      linarith [hk]
    by_cases h30 : k > 0 
    · -- Assume k > 0, so k ≥ 1 
      have h31 : k ≥ 1 := by 
        omega 
      have h32 : (k : ℝ) ≥ (1 : ℝ) := by 
        exact_mod_cast h31 
      nlinarith [Real.pi_pos, h29, Real.pi_pos, h]
    by_cases h31 : k = 0 
    · -- Assume k = 0 
      have hk0 : (k : ℝ) = (0 : ℝ) := by 
        exact_mod_cast h31 
      rw [hk0] at h29 
      nlinarith [Real.pi_pos]
    · -- Assume k < 0 
      have h34 : k < 0 := by 
        omega 
      have h35 : k ≤ -1 := by 
        omega 
      have h36 : (k : ℝ) ≤ (-1 : ℝ) := by 
        exact_mod_cast h35 
      nlinarith [Real.pi_pos, h29, Real.pi_pos, h]