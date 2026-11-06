import Mathlib

open Real

theorem inequalities_315284 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : 2 * c > a + b) :
    c^2 > a * b ∧ c - sqrt (c^2 - a * b) < a ∧ a < c + sqrt (c^2 - a * b) := by

  have h1 : c^2 > a * b := by
    nlinarith [sq_nonneg (c - (a + b) / 2), sq_nonneg (a - b), sq_nonneg (c - a), sq_nonneg (c - b), mul_pos ha hb]
  
  have h2 : c^2 - a * b > 0 := by linarith [h1]

  have h3 : c - Real.sqrt (c^2 - a * b) < a := by
    have h4 : Real.sqrt (c^2 - a * b) ≥ 0 := Real.sqrt_nonneg (c^2 - a * b)
    nlinarith [Real.sqrt_nonneg (c^2 - a * b), Real.sq_sqrt (show 0 ≤ c^2 - a * b by linarith), sq_nonneg (c - a), sq_nonneg (b - a), sq_nonneg (c - (a + b) / 2), sq_nonneg (a - b), mul_pos ha hb, h]

  have h5 : a < c + Real.sqrt (c^2 - a * b) := by
    have h4 : Real.sqrt (c^2 - a * b) ≥ 0 := Real.sqrt_nonneg (c^2 - a * b)
    nlinarith [Real.sqrt_nonneg (c^2 - a * b), Real.sq_sqrt (show 0 ≤ c^2 - a * b by linarith), sq_nonneg (c - a), sq_nonneg (b - a), sq_nonneg (c - (a + b) / 2), sq_nonneg (a - b), mul_pos ha hb, h]

  constructor
  · linarith [h1]
  constructor
  · linarith [h3]
  · linarith [h5]