import Mathlib

theorem inequalities_264272 (a1 a2 b1 b2 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (h1 : a1 > a2) (hb1 : b1 ≥ a1) (hb2 : b1 * b2 ≥ a1 * a2) :
    b1 + b2 ≥ a1 + a2 := by
  nlinarith [sq_nonneg (b1 - a1), sq_nonneg (b2 - a2), sq_nonneg (b1 - b2), sq_nonneg (a1 - a2), 
    mul_pos ha1 ha2
  ]