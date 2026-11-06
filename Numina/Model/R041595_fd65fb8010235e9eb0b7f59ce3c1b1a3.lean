import Mathlib

open Real

theorem algebra_184591 {f : ℝ → ℝ} (hf : ∀ x, f x = (x + abs x) / 2) :
    ∀ x, f (f x) = if x ≥ 0 then x else 0 := by
  intro x 
  by_cases h : x ≥ 0 
  · -- If x ≥ 0, need to prove f (f x) = x 
    have hx1 : f x = x := by 
      rw [hf]
      rw [abs_of_nonneg h]
      all_goals ring_nf 
      <;> linarith
    rw [hx1] 
    simp [h]
    all_goals try { linarith }
    all_goals try { tauto }
  · -- Case where x < 0
    have h1 : f x = (0 : ℝ) := by
      rw [hf]
      rw [abs_of_neg (show x < 0 by linarith)]
      all_goals ring_nf 
      <;> linarith
    rw [h1]
    have h2 : f (0 : ℝ) = (0 : ℝ) := by 
      rw [hf]
      norm_num [abs_of_nonneg]
      all_goals try { linarith }
      all_goals try { tauto }
    rw [h2]
    all_goals try { simp [abs_of_nonneg (show (0 : ℝ) ≥ 0 by trivial), h] }
    all_goals try { linarith }
    all_goals try { tauto }