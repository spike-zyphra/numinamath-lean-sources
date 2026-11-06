import Mathlib

theorem inequalities_177131 (a b c : ℝ) 
    (ha : a^2 ≤ 1) (hb : b^2 ≤ 1) (hc : c^2 ≤ 1) (habc : (a + b + c)^2 ≤ 9) :
    Real.sqrt (1 - a^2) + Real.sqrt (1 - b^2) + Real.sqrt (1 - c^2) ≤
    Real.sqrt (9 - (a + b + c)^2) := by
  have h1 : 0 ≤ Real.sqrt (1 - a^2) := Real.sqrt_nonneg (1 - a^2)
  have h2 : 0 ≤ Real.sqrt (1 - b^2) := Real.sqrt_nonneg (1 - b^2)
  have h3 : 0 ≤ Real.sqrt (1 - c^2) := Real.sqrt_nonneg (1 - c^2)
  have h4 : 0 ≤ Real.sqrt (9 - (a + b + c)^2) := Real.sqrt_nonneg (9 - (a + b + c)^2)
  have h5 : (Real.sqrt (1 - a^2) + Real.sqrt (1 - b^2) + Real.sqrt (1 - c^2)) ^ 2 ≤ (Real.sqrt (9 - (a + b + c) ^ 2)) ^ 2 := by
    have h6 : (Real.sqrt (1 - a^2) + Real.sqrt (1 - b^2) + Real.sqrt (1 - c^2)) ^ 2 =
      (Real.sqrt (1 - a^2)) ^ 2 + (Real.sqrt (1 - b^2)) ^ 2 + (Real.sqrt (1 - c^2)) ^ 2 + 2 * (Real.sqrt (1 - a^2) * Real.sqrt (1 - b^2) + Real.sqrt (1 - a^2) * Real.sqrt (1 - c^2) + Real.sqrt (1 - b^2) * Real.sqrt (1 - c^2)) := by ring
    have h7 : (Real.sqrt (9 - (a + b + c) ^ 2)) ^ 2 = 9 - (a + b + c) ^ 2 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h8 : (Real.sqrt (1 - a^2)) ^ 2 = 1 - a^2 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h9 : (Real.sqrt (1 - b^2)) ^ 2 = 1 - b^2 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h10 : (Real.sqrt (1 - c^2)) ^ 2 = 1 - c^2 := by
      rw [Real.sq_sqrt]
      nlinarith
    rw [h6, h7, h8, h9, h10]
    nlinarith [sq_nonneg (Real.sqrt (1 - a^2) - Real.sqrt (1 - b^2)), sq_nonneg (Real.sqrt (1 - a^2) - Real.sqrt (1 - c^2)), sq_nonneg (Real.sqrt (1 - b^2) - Real.sqrt (1 - c^2)), sq_nonneg (a + b + c - (Real.sqrt (1 - a^2) + Real.sqrt (1 - b^2) + Real.sqrt (1 - c^2))), 
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), Real.sqrt_nonneg (1 - a^2), Real.sqrt_nonneg (1 - b^2), Real.sqrt_nonneg (1 - c^2),
      mul_nonneg (Real.sqrt_nonneg (1 - a^2)) (Real.sqrt_nonneg (1 - b^2)), 
      mul_nonneg (Real.sqrt_nonneg (1 - a^2)) (Real.sqrt_nonneg (1 - c^2)), 
      mul_nonneg (Real.sqrt_nonneg (1 - b^2)) (Real.sqrt_nonneg (1 - c^2)), 
      Real.sq_sqrt (show 0 ≤ (1 - a^2 : ℝ) by nlinarith), 
      Real.sq_sqrt (show 0 ≤ (1 - b^2 : ℝ) by nlinarith), 
      Real.sq_sqrt (show 0 ≤ (1 - c^2 : ℝ) by nlinarith)
    ]
  have h11 : Real.sqrt (1 - a^2) + Real.sqrt (1 - b^2) + Real.sqrt (1 - c^2) ≤ Real.sqrt (9 - (a + b + c) ^ 2) := by
    have h12 : 0 ≤ Real.sqrt (9 - (a + b + c) ^ 2) := Real.sqrt_nonneg (9 - (a + b + c) ^ 2)
    have h13 : (Real.sqrt (1 - a^2) + Real.sqrt (1 - b^2) + Real.sqrt (1 - c^2)) ^ 2 ≤ (Real.sqrt (9 - (a + b + c) ^ 2)) ^ 2 := h5
    have h14 : Real.sqrt (1 - a^2) + Real.sqrt (1 - b^2) + Real.sqrt (1 - c^2) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (9 - (a + b + c) ^ 2)]
  linarith [h11]