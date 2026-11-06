import Mathlib

theorem algebra_88511 {b c d : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^3 + b*x^2 + c*x + d)
    (h : f (-1) = 0) (h' : f 1 = 0) (h'' : f 0 = 2) :
    b = -2 := by 
  simp [hf] at h h' h''
  linarith