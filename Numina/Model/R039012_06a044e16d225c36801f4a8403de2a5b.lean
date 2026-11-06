import Mathlib

theorem inequalities_310799 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.sqrt (3 * x * (x + y) * (y + z)) +
    Real.sqrt (3 * y * (y + z) * (z + x)) +
    Real.sqrt (3 * z * (z + x) * (x + y)) ≤
    Real.sqrt (4 * (x + y + z)^3) := by

  have h1 : 0 ≤ (3 * x * (x + y) * (y + z) : ℝ) := by positivity
  have h2 : 0 ≤ (3 * y * (y + z) * (z + x) : ℝ) := by positivity
  have h3 : 0 ≤ (3 * z * (z + x) * (x + y) : ℝ) := by positivity
  have h4 : 0 ≤ (4 * (x + y + z) ^ 3 : ℝ) := by positivity

  have h5 : (Real.sqrt (3 * x * (x + y) * (y + z)) + 
    Real.sqrt (3 * y * (y + z) * (z + x)) + 
    Real.sqrt (3 * z * (z + x) * (x + y))
    ) ^ 2 ≤ 4 * (x + y + z) ^ 3 := by
    have h7 : (Real.sqrt (3 * x * (x + y) * (y + z)))^2 = 3 * x * (x + y) * (y + z) := by
      rw [Real.sq_sqrt]
      nlinarith
    have h8 : (Real.sqrt (3 * y * (y + z) * (z + x)))^2 = 3 * y * (y + z) * (z + x) := by
      rw [Real.sq_sqrt]
      positivity
    have h9 : (Real.sqrt (3 * z * (z + x) * (x + y)))^2 = 3 * z * (z + x) * (x + y) := by
      rw [Real.sq_sqrt]
      positivity

    nlinarith [sq_nonneg (Real.sqrt (3 * x * (x + y) * (y + z)) - Real.sqrt (3 * y * (y + z) * (z + x))), sq_nonneg (Real.sqrt (3 * y * (y + z) * (z + x)) - Real.sqrt (3 * z * (z + x) * (x + y))), sq_nonneg (Real.sqrt (3 * x * (x + y) * (y + z)) - Real.sqrt (3 * z * (z + x) * (x + y))), Real.sqrt_nonneg (3 * x * (x + y) * (y + z)), Real.sqrt_nonneg (3 * y * (y + z) * (z + x)), Real.sqrt_nonneg (3 * z * (z + x) * (x + y)), 
      mul_nonneg (Real.sqrt_nonneg (3 * x * (x + y) * (y + z))) (Real.sqrt_nonneg (3 * y * (y + z) * (z + x))), 
      mul_nonneg (Real.sqrt_nonneg (3 * x * (x + y) * (y + z))) (Real.sqrt_nonneg (3 * z * (z + x) * (x + y))), 
      mul_nonneg (Real.sqrt_nonneg (3 * y * (y + z) * (z + x))) (Real.sqrt_nonneg (3 * z * (z + x) * (x + y))), 
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
      mul_pos hx (show 0 < x + y by linarith), 
      mul_pos (show 0 < x + y by linarith) (show 0 < y + z by linarith), 
      mul_pos (show 0 < y + z by linarith) (show 0 < z + x by linarith), 
      mul_pos (show 0 < z + x by linarith) (show 0 < x + y by linarith)
    ]
  have h6 : Real.sqrt ( (Real.sqrt (3 * x * (x + y) * (y + z)) + Real.sqrt (3 * y * (y + z) * (z + x)) + Real.sqrt (3 * z * (z + x) * (x + y)) ) ^ 2 ) ≤ Real.sqrt (4 * (x + y + z)^3) := by
    apply Real.sqrt_le_sqrt 
    linarith [h5]

  have h8 : Real.sqrt ( (Real.sqrt (3 * x * (x + y) * (y + z)) + Real.sqrt (3 * y * (y + z) * (z + x)) + Real.sqrt (3 * z * (z + x) * (x + y))
    ) ^ 2 ) = Real.sqrt (3 * x * (x + y) * (y + z)) + Real.sqrt (3 * y * (y + z) * (z + x)) + Real.sqrt (3 * z * (z + x) * (x + y)) := by 
    rw [Real.sqrt_sq (show 0 ≤ Real.sqrt (3 * x * (x + y) * (y + z)) + Real.sqrt (3 * y * (y + z) * (z + x)) + Real.sqrt (3 * z * (z + x) * (x + y)) by positivity)]
  linarith [h6, h8]