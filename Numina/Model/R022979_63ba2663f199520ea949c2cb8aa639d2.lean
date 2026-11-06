import Mathlib

theorem inequalities_197700 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt ((a + c) * (b + d)) ≥ Real.sqrt (a * b) + Real.sqrt (c * d) := by
  have h1 : Real.sqrt ((a + c) * (b + d)) ^ 2 ≥ (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 := by
    have h2 : Real.sqrt ((a + c) * (b + d)) ^ 2 = (a + c) * (b + d) := by
      rw [Real.sq_sqrt]
      positivity
    have h3 : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 = (Real.sqrt (a * b)) ^ 2 + (Real.sqrt (c * d)) ^ 2 + 2 * (Real.sqrt (a * b) * Real.sqrt (c * d)) := by
      ring
    have h4 : (Real.sqrt (a * b)) ^ 2 = a * b := by
      rw [Real.sq_sqrt]
      nlinarith
    have h5 : (Real.sqrt (c * d)) ^ 2 = c * d := by
      rw [Real.sq_sqrt]
      nlinarith
    have h6 : Real.sqrt (a * b) * Real.sqrt (c * d) = Real.sqrt (a * b * (c * d)) := by
      rw [← Real.sqrt_mul (by positivity)]
      all_goals ring_nf
      all_goals positivity
    rw [h2, h3, h4, h5, h6]
    nlinarith [sq_nonneg (Real.sqrt (a * b) - Real.sqrt (c * d)), sq_nonneg (a * d - b * c),
      Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d),
      sq_nonneg (a * b - c * d), sq_nonneg ( (a + c) * (b + d) - (a * b + c * d + 2 * Real.sqrt (a * b * (c * d)) ) ), 
      mul_nonneg (show 0 ≤ (Real.sqrt (a * b) : ℝ) by positivity) (show 0 ≤ (Real.sqrt (c * d) : ℝ) by positivity),
      mul_nonneg (show 0 ≤ (a : ℝ) by linarith) (show 0 ≤ (b : ℝ) by linarith), 
      mul_nonneg (show 0 ≤ (a : ℝ) by linarith) (show 0 ≤ (d : ℝ) by linarith), 
      mul_nonneg (show 0 ≤ (c : ℝ) by linarith) (show 0 ≤ (b : ℝ) by linarith), 
      mul_nonneg (show 0 ≤ (c : ℝ) by linarith) (show 0 ≤ (d : ℝ) by linarith), 
      Real.sq_sqrt (show 0 ≤ ( (a * b * (c * d)) : ℝ) by positivity)
    ]
  have h2 : 0 ≤ Real.sqrt ((a + c) * (b + d)) := by positivity
  have h3 : 0 ≤ Real.sqrt (a * b) + Real.sqrt (c * d) := by positivity
  nlinarith [h1, Real.sqrt_nonneg ((a + c) * (b + d)), Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d)]