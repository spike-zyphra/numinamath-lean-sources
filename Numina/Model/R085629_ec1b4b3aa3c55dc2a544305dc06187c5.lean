import Mathlib

theorem algebra_258115 (t : ℝ) (h : 0 ≤ 24 - t^2 ∧ 0 ≤ 8 - t^2) :
    Real.sqrt (24 - t^2) - Real.sqrt (8 - t^2) = 2 →
    Real.sqrt (24 - t^2) + Real.sqrt (8 - t^2) = 8 := by

  intro h1

  have ha2 : (Real.sqrt (24 - t^2)) ^ 2 = 24 - t^2 := by
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 24 - t ^ 2 by linarith [h.1])
  have hb2 : (Real.sqrt (8 - t^2)) ^ 2 = 8 - t^2 := by
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 8 - t ^ 2 by linarith [h.2])
  have hab2 : (Real.sqrt (24 - t^2)) ^ 2 - (Real.sqrt (8 - t^2)) ^ 2 = 16 := by
    linarith [ha2, hb2]
  
  have hab : Real.sqrt (24 - t^2) - Real.sqrt (8 - t^2) = 2 := h1
  have hab2_eq : (Real.sqrt (24 - t^2)) ^ 2 - (Real.sqrt (8 - t^2)) ^ 2 =
      (Real.sqrt (24 - t^2) - Real.sqrt (8 - t^2)) * (Real.sqrt (24 - t^2) + Real.sqrt (8 - t^2)) := by
    ring
  rw [hab2_eq] at hab2
  rw [hab] at hab2

  have : Real.sqrt (24 - t^2) + Real.sqrt (8 - t^2) = 8 := by
    linarith
  
  linarith