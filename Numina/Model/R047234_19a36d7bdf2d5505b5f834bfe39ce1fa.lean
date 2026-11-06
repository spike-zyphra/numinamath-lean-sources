import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_114077 {f g : ℝ → ℝ}
  (hf : ∀ x > 0, f (x / 3) + 2 ≤ logb 3 x ∧ logb 3 x ≤ g x - 1)
  (hg : ∀ x > 0, g (x / 3) ≤ logb 3 x ∧ logb 3 x ≤ f x + 1) :
  ∀ x > 0, f x = logb 3 x - 1 ∧ g x = logb 3 x + 1 := by 
  intro x hx
  have h1 := hf (3 * x) (by linarith)
  have h2 := hf x hx 
  have h3 := hg (3 * x) (by linarith)
  have h4 := hg x hx 
  have h5 : f x ≤ logb 3 x - 1 := by
    have h6 : f ((3 * x) / 3) + 2 ≤ logb 3 (3 * x) := by 
      apply (hf (3 * x) (by linarith)).left 
    have h7 : (3 * x) / 3 = x := by 
      ring 
    have h8 : f ((3 * x) / 3) = f x := by 
      rw [h7] 
    have h9 : logb 3 (3 * x) = logb 3 3 + logb 3 x := by 
      rw [logb_mul (by norm_num) (by linarith)]
    have h10 : logb 3 (3 : ℝ) = 1 := by
      rw [logb_self_eq_one]
      all_goals norm_num 
    linarith [h6, h8, h9, h10] 
  have h5' : logb 3 x - 1 ≤ f x := by 
    have h11 : logb 3 x ≤ f x + 1 := by
      apply (hg x hx).right 
    linarith 
  have hf_eq : f x = logb 3 x - 1 := by 
    linarith [h5, h5']
  have h7 : g x ≥ logb 3 x + 1 := by
    have h11 : logb 3 x ≤ g x - 1 := by
      apply (hf x hx).right 
    linarith 
  have h8 : g x ≤ 1 + logb 3 x := by 
    have h12 : g ((3 * x) / 3) ≤ logb 3 (3 * x) := by 
      apply (hg (3 * x) (by linarith)).left 
    have h13 : (3 * x) / 3 = x := by 
      ring 
    have h14 : g ((3 * x) / 3) = g x := by
      rw [h13] 
    have h15 : logb 3 (3 * x) = 1 + logb 3 x := by 
      calc 
        logb 3 (3 * x) = logb 3 3 + logb 3 x := by 
          rw [logb_mul (by norm_num) (by linarith)]
        _ = 1 + logb 3 x := by 
          have h16 : logb 3 (3 : ℝ) = 1 := by 
            rw [logb_self_eq_one]
            all_goals norm_num 
          linarith 
    linarith [h12, h14, h15] 
  have h8' : g x = logb 3 x + 1 := by 
    linarith [h7, h8] 
  constructor 
  · exact hf_eq 
  · exact h8'