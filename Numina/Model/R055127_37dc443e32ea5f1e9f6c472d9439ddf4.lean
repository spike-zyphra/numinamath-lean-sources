import Mathlib

theorem algebra_210005 (x : ℝ) (hx : x > 0) (h : (1 - 30 / 100) * x = (1 + 20 / 100) * (x + 20)) :
    (1 + 20 / 100) * (x + 20) ≥ x + 15 := by
  nlinarith -- solves the contradiction in the hypotheses