import Mathlib


theorem algebra_7718 (f : ℝ → ℝ) (hf : f = fun x => x ^ 3 + x + 2014)
    (line : ℝ → ℝ) (hline : line = fun x => m * x + b) (m b : ℝ)
    (h : line 20 = f 20) (h' : line 14 = f 14) :
    line (-34) = f (-34) := by

  simp [hf, hline] at h h' ⊢
  linarith