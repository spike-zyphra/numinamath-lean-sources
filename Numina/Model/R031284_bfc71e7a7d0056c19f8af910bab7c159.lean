import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9314 {f g : ℝ → ℝ} (hf : f = λ x => if x < 0 then x else x^2) (hg : g = λ x => if x < 0 then x else sqrt x) : Function.LeftInverse g f ∧ Function.RightInverse g f := by
  constructor 
  · -- Show g is a left inverse of f 
    intro y
    have g1: g (f y) = y := by
      rw [hf, hg]
      by_cases h1 : y < (0 : ℝ)
      · -- y < 0
        simp [if_pos h1, if_pos h1]
      · -- y ≥ 0 
        have h2 : y ≥ (0 : ℝ) := by linarith
        have h6a : sqrt (y^2) = y := Real.sqrt_sq (by linarith)
        have h14a : ((λ x : ℝ => if x < 0 then x else sqrt x) ((λ x : ℝ => if x < 0 then x else x^2) y)) = y := by
          have hf_y : ((λ x : ℝ => if x < 0 then x else x^2) y) = y ^ 2 := by 
            simp [show ¬(y < (0 : ℝ)) by linarith]
          rw [hf_y]
          have h8 : (y ^ 2 < (0 : ℝ)) = False := by
            have h15 : y ^ 2 ≥ (0 : ℝ) := by nlinarith 
            simp [h15]
          simp [h8, if_false, Real.sqrt_nonneg]
          all_goals
            try { 
              nlinarith [Real.sqrt_nonneg (y ^ 2), Real.sq_sqrt (show (y ^ 2) ≥ 0 by nlinarith), Real.mul_self_sqrt (show (y) ≥ 0 by nlinarith)]
            }
        simpa using h14a 
    simpa using g1 
  · -- Show g is a right inverse of f 
    intro x 
    have g2: (f (g x)) = x := by 
      by_cases h1 : x < (0 : ℝ) 
      · -- Case x < 0 
        simp [hf, hg, if_pos h1]
      · -- Case x ≥ 0 
        have h2: x ≥ (0 : ℝ) := by linarith 
        have h3: (g x) = sqrt x := by 
          simp [hg, h2]
        rw [h3]
        have h5: (sqrt x) ≥ (0 : ℝ) := Real.sqrt_nonneg x 
        have h6 : f (sqrt x) = (sqrt x) ^ 2 := by
          rw [hf]
          have hnot : ¬ (sqrt x < (0 : ℝ)) := by
            linarith [Real.sqrt_nonneg x]
          simp only [hnot, if_false, not_lt]
        have h10 : (sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
        rw [h6, h10]
    simpa using g2