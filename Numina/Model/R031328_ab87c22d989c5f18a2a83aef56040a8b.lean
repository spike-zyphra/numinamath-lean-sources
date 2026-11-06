import Mathlib

open Real

theorem algebra_9315 {f : ℝ → ℝ} (hf : f = λ x => (cos x) ^ 2) :
IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi) := by
  constructor 
  · -- Show that π is indeed a positive period of f
    constructor 
    · -- Show that π > 0 
      exact Real.pi_pos 
    · -- Show that f = λ x => f (x + π)
      funext x
      rw [hf]
      simp [Real.cos_add_pi]
  · -- Show that π is the smallest positive period
    intro T ⟨ht_pos, ht_period⟩
    by_contra h 
    push_neg at h 
    have eq1 := congr_fun ht_period (Real.pi / 2 - T)
    simp [hf] at eq1 
    -- We get from eq1 that `sin T ^ 2 = 0`, from equality above.
    have h2 : (sin T) ^ 2 = 0 := by
      have eq1' : cos (Real.pi / 2 - T) ^ 2 = cos (Real.pi / 2) ^ 2 := by 
        simpa using eq1 
      have h1 : cos (Real.pi / 2 - T) = sin T := by 
        rw [cos_pi_div_two_sub] 
      have h0 : cos (Real.pi / 2) = (0 : ℝ) := cos_pi_div_two 
      rw [h1, h0] at eq1' 
      linarith 
    -- This implies sin T = 0
    have h3 : sin T = 0 := by 
      nlinarith 
    -- But sin T > 0 for 0 < T < π (strict inequality)
    -- contradiction
    have h4 : 0 < T := ht_pos 
    have h5 : T < Real.pi := by linarith 
    have h6 : sin T > 0 := by
      apply sin_pos_of_pos_of_lt_pi 
      all_goals 
      linarith 
    linarith  -- contradiction