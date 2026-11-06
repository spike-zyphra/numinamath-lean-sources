import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_302394 {f : ℝ → ℝ} (hf : f = λ x => (cos x)^4 + (sin x)^2) :
    IsLeast {x | 0 < x ∧ f = λ y => f (y + x)} (π / 2) := by
  constructor
  · -- π / 2 is in the set.
    constructor
    · -- Show that π / 2 > 0.
      have h1 : 0 < π / 2 := by
        linarith [Real.pi_pos]
      exact h1
    · -- Show that f = fun y => f (y + π / 2)
      funext y
      rw [hf]
      have h1 : (cos y) ^ 4 + (sin y) ^ 2 = (cos (y + π / 2)) ^ 4 + (sin (y + π / 2)) ^ 2 := by
        have h2 : cos (y + π / 2) = - sin y := by 
          rw [cos_add, cos_pi_div_two, sin_pi_div_two]
          ring
        have h3 : sin (y + π / 2) = cos y := by 
          rw [sin_add, cos_pi_div_two, sin_pi_div_two]
          ring
        rw [h2, h3]
        have h4 : (cos y) ^ 4 + (sin y) ^ 2 = (-sin y) ^ 4 + (cos y) ^ 2 := by 
          nlinarith [sq_nonneg (cos y ^ 2 - sin y ^ 2), sq_nonneg (cos y), sq_nonneg (sin y), Real.cos_sq_add_sin_sq y]
        linarith [h4]
      simpa using h1
  · -- π / 2 is the least element in the set.
    intro x h
    rcases h with ⟨hx_pos, h_eq⟩
    by_contra h'
    push_neg at h'
    have h1 := congr_fun h_eq ((π / 2) - x)
    have eq1 : f ((π / 2) - x) = f (π / 2) := by 
      have h1' : f ((π / 2) - x) = f ((π / 2) - x + x) := by 
        simpa using h1
      have h2 : (π / 2 : ℝ) - x + x = π / 2 := by 
        ring_nf
      rw [h2] at h1'
      linarith [h1']
    rw [hf] at eq1 
    simp [show cos (π / 2 : ℝ) = 0 by rw [cos_pi_div_two], 
          show sin (π / 2 : ℝ) = 1 by rw [sin_pi_div_two], 
          show cos ((π / 2 : ℝ) - x) = sin x by rw [cos_pi_div_two_sub], 
          show sin ((π / 2 : ℝ) - x) = cos x by rw [sin_pi_div_two_sub]] at eq1 
    have eq2 : sin x ^ 2 * (sin x ^ 2 - 1) = 0 := by 
      nlinarith [sq_nonneg (sin x ^ 2 - 1), sq_nonneg (cos x ^ 2 - 0), Real.sin_sq_add_cos_sq x]
    cases' (mul_eq_zero.mp eq2) with h1 h2
    · -- Case sin x ^ 2 = 0
      have h3 : sin x ^ 2 = 0 := by 
        linarith 
      have h4 : sin x = 0 := by 
        nlinarith 
      have h5 : sin x > 0 := by 
        apply sin_pos_of_pos_of_lt_pi
        · -- 0 < x
          linarith 
        · -- x < π
          nlinarith [Real.pi_gt_three, Real.pi_pos, h']
      linarith
    · -- Case sin x ^ 2 - 1 = 0
      have h3 : sin x ^ 2 = 1 := by 
        linarith 
      have h4 : sin x < 1 := by
        have h7 : sin x < sin (π / 2 : ℝ) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals 
            nlinarith [Real.pi_gt_three, Real.pi_pos, h', hx_pos]
        have h8 : sin (π / 2 : ℝ) = 1 := by 
          rw [sin_pi_div_two]
        linarith [h7, h8]
      have h5 : sin x ^ 2 < 1 := by 
        have h6 : sin x > 0 := by 
          apply sin_pos_of_pos_of_lt_pi
          · -- 0 < x
            linarith 
          · -- x < π
            nlinarith [Real.pi_gt_three, Real.pi_pos, h']
        nlinarith [h4, h6]
      linarith