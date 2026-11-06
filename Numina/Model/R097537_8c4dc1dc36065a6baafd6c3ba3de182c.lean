import Mathlib
open Real

theorem algebra_8903
  (f : ℝ → ℝ)
  (h : ∀ x y z, (1 / 3) * f (x * y) + (1 / 3) * f (x * z) - f x * f (y * z) ≥ 1 / 9) :
  ∑ i ∈ Finset.range 100, ⌊(i + 1) * f (i + 1)⌋ = 1650 := by

  have h1 : f 0 = 1 / 3:= by
    specialize h 0 0 0
    simp at h
    nlinarith [sq_nonneg (f 0 - 1 / 3)]
  
  have h2 : ∀ x : ℝ, f x ≤ 1 / 3:= by
    intro x
    specialize h x 0 0
    simp [h1] at h
    nlinarith
  
  have h3 : f 1 = 1 / 3:= by
    specialize h 1 1 1
    simp at h
    nlinarith [sq_nonneg (f 1 - 1 / 3)]
  
  have h4 : ∀ x : ℝ, f x ≥ 1 / 3:= by 
    intro x
    specialize h x 1 1
    simp [h3] at h
    nlinarith
  
  have h5 : ∀ x : ℝ, f x = 1 / 3:= by 
    intro x
    have hfx1 : f x ≤ 1 / 3:= h2 x
    have hfx2 : f x ≥ 1 / 3:= h4 x
    linarith
  
  norm_num [Finset.sum_range_succ, h5]
  <;> try { norm_num }