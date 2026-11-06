import Mathlib

open Matrix

theorem calculus_14120 (a b c d : ℝ) 
    (h : Matrix.det !![a, b; c, d] = 5) :
    Matrix.det !![a-c, b-d; c, d] = 5 := by 
  simp at *
  linarith