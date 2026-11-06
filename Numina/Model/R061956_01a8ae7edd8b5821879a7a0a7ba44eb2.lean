import Mathlib

theorem algebra_277133 (S P T : ℝ) (hS : S = 4.20) (hP : P = 7.60) (hT : T = 3.20)
    (h : (S + P + T) * 1.05 = x) : x = 15.75 := by 
  rw [hS, hP, hT] at h
  linarith