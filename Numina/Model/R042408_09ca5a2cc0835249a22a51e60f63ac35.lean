import Mathlib

theorem algebra_215009 {x y : ℝ} (hx : 2 ≤ 3 * x) (hy : 2 ≤ 3 * y)
    (h1 : x ^ 2 - 4 * Real.sqrt (3 * x - 2) + 6 = y) (h2 : y ^ 2 - 4 * Real.sqrt (3 * y - 2) + 6 = x) :
    x = 2 ∧ y = 2 := by
  have h3 : 0 ≤ 3 * x - 2 := by linarith
  have h4 : 0 ≤ 3 * y - 2 := by linarith
  have h5 : 0 ≤ (3 * x - 2 : ℝ) := by linarith
  have h6 : 0 ≤ (3 * y - 2 : ℝ) := by linarith
  have h7 : (Real.sqrt (3 * x - 2)) ^ 2 = 3 * x - 2 := by
    rw [Real.sq_sqrt]
    linarith
  have h8 : (Real.sqrt (3 * y - 2)) ^ 2 = 3 * y - 2 := by
    rw [Real.sq_sqrt]
    linarith
  have h9 : (x - 2) ^ 2 + (y - 2) ^ 2 = 0 := by
    nlinarith [Real.sqrt_nonneg (3 * x - 2), Real.sqrt_nonneg (3 * y - 2), 
          sq_nonneg (Real.sqrt (3 * x - 2) - 2), sq_nonneg (Real.sqrt (3 * y - 2) - 2),
          mul_nonneg (Real.sqrt_nonneg (3 * x - 2)) (Real.sqrt_nonneg (3 * y - 2)), 
        sq_nonneg (x - y), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 * x - 2 by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 * y - 2 by linarith)
        ]
  have hx2 : (x - 2) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 2), sq_nonneg (y - 2), h9]
  have hy2 : (y - 2) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 2), sq_nonneg (y - 2), h9]
  have hx0 : x - 2 = 0 := by
    nlinarith
  have hy0 : y - 2 = 0 := by 
    nlinarith
  have hx1 : x = 2 := by linarith
  have hy1 : y = 2 := by linarith
  exact ⟨hx1, hy1⟩