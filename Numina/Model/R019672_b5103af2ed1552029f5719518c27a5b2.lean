import Mathlib

open Real

theorem inequalities_601044 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    sqrt (9 - 8 * a^2) + sqrt (9 - 8 * b^2) + sqrt (9 - 8 * c^2) ≥ 7 := by
  have h1 : c = 1 - a - b := by linarith
  rw [h1] at *
  have h7 : sqrt (9 - 8 * a^2) ≥ 1 + 2 * (1 - a) := by
    have h8 : Real.sqrt (9 - 8 * a^2) ≥ 1 + 2 * (1 - a) := by
      have h9 : 0 ≤ a := by linarith
      have h10 : a ≤ 1 := by nlinarith
      have h11 : (9 - 8 * a^2 : ℝ) ≥ 0 := by nlinarith
      nlinarith [Real.sqrt_nonneg (9 - 8 * a^2), 
          Real.sq_sqrt (show (9 - 8 * a^2 : ℝ) ≥ 0 by nlinarith), 
          sq_nonneg (Real.sqrt (9 - 8 * a^2) - (1 + 2 * (1 - a)))
        ]
    linarith
  have h8 : sqrt (9 - 8 * b^2) ≥ 1 + 2 * (1 - b) := by
    have h9 : Real.sqrt (9 - 8 * b^2) ≥ 1 + 2 * (1 - b) := by
      have h10 : 0 ≤ b := by linarith
      have h11 : b ≤ 1 := by nlinarith
      have h12 : (9 - 8 * b^2 : ℝ) ≥ 0 := by nlinarith
      nlinarith [Real.sqrt_nonneg (9 - 8 * b^2), 
          Real.sq_sqrt (show (9 - 8 * b^2 : ℝ) ≥ 0 by nlinarith), 
          sq_nonneg (Real.sqrt (9 - 8 * b^2) - (1 + 2 * (1 - b)))
        ]
    linarith
  have h9 : sqrt (9 - 8 * (1 - a - b) ^2) ≥ 1 + 2 * (1 - (1 - a - b)) := by
    have h10 : Real.sqrt (9 - 8 * (1 - a - b) ^2) ≥ 1 + 2 * (1 - (1 - a - b)) := by
      have h11 : 0 ≤ (1 - a - b : ℝ) := by nlinarith
      have h12 : (1 - a - b : ℝ) ≤ 1 := by nlinarith
      have h13 : (9 - 8 * (1 - a - b) ^2 : ℝ) ≥ 0 := by nlinarith
      nlinarith [Real.sqrt_nonneg (9 - 8 * (1 - a - b) ^2), 
          Real.sq_sqrt (show (9 - 8 * (1 - a - b) ^2 : ℝ) ≥ 0 by nlinarith), 
          sq_nonneg (Real.sqrt (9 - 8 * (1 - a - b) ^2) - (1 + 2 * (1 - (1 - a - b))))
        ]
    linarith
  have h10 : (1 : ℝ) + 2 * (1 - (1 - a - b)) = 1 + 2 * (a + b) := by
    linarith
  have h11 : sqrt (9 - 8 * (1 - a - b) ^2) ≥ 1 + 2 * (a + b) := by
    linarith [h9, h10]
  have h12 : sqrt (9 - 8 * a^2) + sqrt (9 - 8 * b^2) + sqrt (9 - 8 * (1 - a - b)^2) ≥ 7 := by
    linarith [h7, h8, h11]
  linarith [h12]