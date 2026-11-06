import Mathlib

open Real


theorem algebra_9407 {f : ℝ → ℝ}
(hodd : ∀ x, f x = - f (-x)) (hf : ∀ x < 0, f x = -x * logb 2 (2 - x)) :
∀ x, f x = if x < 0 then -x * logb 2 (2 - x) else -x * logb 2 (2 + x) := by
  intro x; split_ifs with hx
  apply hf; assumption
  have h1 : -x ≤ (0 : ℝ) := by linarith
  have h2 : f x = -f (-x) := by 
    specialize hodd x
    linarith
  by_cases h4 : -x < (0 : ℝ)
  · 
    have h3 : f (-x) = -(-x) * logb 2 (2 - (-x)) := by
      apply hf
      linarith
    rw [h2, h3]
    ring_nf
    <;> simp [show (2:ℝ) - (-x) = 2 + x by ring]
    <;> ring_nf
  · 
    have h6 : -x = (0 : ℝ) := by linarith
    have h7 : x = (0 : ℝ) := by linarith
    rw [h7]
    have h8 : f 0 = (0 : ℝ) := by 
      have h9 : f 0 = - f (-0) := by 
        specialize hodd 0
        simpa using hodd
      have h10 : f (-0) = f 0 := by 
        simp
      rw [h10] at h9
      linarith
    simp [h8]