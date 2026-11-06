import Mathlib

open Real Set

theorem calculus_12802 : arcsin (-1) = -π / 2 := by 
  have h1 : arcsin (-1) = -(Real.pi / 2) := by 
    have h2 : arcsin 1 = Real.pi / 2 := Real.arcsin_one
    have h3 : arcsin (-1) = - arcsin 1 := by 
      rw [Real.arcsin_neg]
    rw [h3, h2]
  linarith [h1]