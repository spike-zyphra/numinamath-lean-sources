import Mathlib

open Set Real

theorem inequalities_267882 (a : ℝ) (A B : Set ℝ)
    (hA : A = {x | abs x ≤ 2}) (hB : B = {x | a ≤ x}) (hAB : A ⊆ B) :
    a ≤ -2 := by
  have h1 : -2 ∈ A := by
    rw [hA]
    norm_num [abs_le]
  
  have h2 : -2 ∈ B := hAB h1
  
  rw [hB] at h2
  
  simp at h2
  
  -- Now we have h2 = a ≤ -2, which is what we need to prove
  linarith