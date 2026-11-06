import Mathlib

theorem algebra_3391 (n : ℤ) (h : n = -12) :
    ∑ i ∈ Finset.Icc n 8, i = -42 := by 
  rw [h]
  rfl