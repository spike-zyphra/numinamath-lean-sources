import Mathlib

theorem inequalities_43775 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 3) :
    6 <  √(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3) ∧
    √(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3) ≤ 3 * √5 := by

  have h2 : √(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3) ≤ 3 * √5 := by
    have h3 : (√(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3)) ^ 2 ≤ 45 := by
      nlinarith [sq_nonneg (√(2 * x + 3) - √(2 * y + 3)), sq_nonneg (√(2 * y + 3) - √(2 * z + 3)), sq_nonneg (√(2 * z + 3) - √(2 * x + 3)),
          Real.sqrt_nonneg (2 * x + 3), Real.sqrt_nonneg (2 * y + 3), Real.sqrt_nonneg (2 * z + 3),
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x + 3 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * y + 3 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * z + 3 by nlinarith),
          mul_nonneg (Real.sqrt_nonneg (2 * x + 3)) (Real.sqrt_nonneg (2 * y + 3)), mul_nonneg (Real.sqrt_nonneg (2 * y + 3)) (Real.sqrt_nonneg (2 * z + 3)), mul_nonneg (Real.sqrt_nonneg (2 * z + 3)) (Real.sqrt_nonneg (2 * x + 3)), hsum]
    have h4 : (√(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3)) ≤ 3 * Real.sqrt 5 := by
      have h5 : (√(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3)) ^ 2 ≤ (3 * Real.sqrt 5) ^ 2 := by
        have h6 : (3 * Real.sqrt 5) ^ 2 = 45 := by
          calc
            (3 * Real.sqrt 5) ^ 2 = 9 * (Real.sqrt 5) ^ 2 := by ring
            _ = 9 * 5 := by rw [Real.sq_sqrt]; positivity
            _ = 45 := by norm_num
        nlinarith
      have h7 : (√(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3)) ≤ (3 * Real.sqrt 5) := by
        have h8 : 0 ≤ (3 * Real.sqrt 5) := by positivity
        nlinarith [Real.sqrt_nonneg (2 * x + 3), Real.sqrt_nonneg (2 * y + 3), Real.sqrt_nonneg (2 * z + 3), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      linarith
    linarith

  have h3 : 6 < √(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3) := by
    have h4 : √(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3) > 6 := by
      have h5 : (√(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3)) ^ 2 > 36 := by
        have h6 : (√(2 * x + 3)) ^ 2 = 2 * x + 3 := Real.sq_sqrt (by nlinarith)
        have h7 : (√(2 * y + 3)) ^ 2 = 2 * y + 3 := Real.sq_sqrt (by nlinarith)
        have h8 : (√(2 * z + 3)) ^ 2 = 2 * z + 3 := Real.sq_sqrt (by nlinarith)
        have h9 : (√(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3)) ^ 2 = (√(2 * x + 3)) ^ 2 + (√(2 * y + 3)) ^ 2 + (√(2 * z + 3)) ^ 2 + 2 * (√(2 * x + 3) * √(2 * y + 3) + √(2 * y + 3) * √(2 * z + 3) + √(2 * z + 3) * √(2 * x + 3)) := by ring
        nlinarith [Real.sqrt_nonneg (2 * x + 3), Real.sqrt_nonneg (2 * y + 3), Real.sqrt_nonneg (2 * z + 3),
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, 
          mul_pos (show 0 < x by linarith) (show 0 < y by linarith), 
          mul_pos (show 0 < y by linarith) (show 0 < z by linarith), 
          mul_pos (show 0 < x by linarith) (show 0 < z by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x + 3 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * y + 3 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * z + 3 by nlinarith), 
          mul_nonneg (Real.sqrt_nonneg (2 * x + 3)) (Real.sqrt_nonneg (2 * y + 3)), 
          mul_nonneg (Real.sqrt_nonneg (2 * y + 3)) (Real.sqrt_nonneg (2 * z + 3)), 
          mul_nonneg (Real.sqrt_nonneg (2 * z + 3)) (Real.sqrt_nonneg (2 * x + 3))
          ]
      have h4 : (√(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3)) > 0 := by positivity
      have h10 : (√(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3)) > 6 := by
        nlinarith [Real.sqrt_nonneg (2 * x + 3), Real.sqrt_nonneg (2 * y + 3), Real.sqrt_nonneg (2 * z + 3)]
      linarith
    linarith

  constructor
  · exact h3
  · exact h2