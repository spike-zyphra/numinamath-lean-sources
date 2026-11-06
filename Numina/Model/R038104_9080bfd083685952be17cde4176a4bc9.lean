import Mathlib

theorem algebra_283921 (x : ℝ) (hx : x ∈ Set.Icc 6 12) :
    (12 - x) + x = 12 := by
  have h2 : 6 ≤ x := by
    have h1 : x ∈ Set.Icc (6 : ℝ) 12 := hx
    simp at h1 ⊢
    linarith [h1.1]

  have h3 : x ≤ 12 := by 
    have h1 : x ∈ Set.Icc (6 : ℝ) 12 := hx
    simp at h1 ⊢
    linarith [h1.2]

  linarith