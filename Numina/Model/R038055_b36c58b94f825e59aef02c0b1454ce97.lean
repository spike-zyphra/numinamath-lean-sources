import Mathlib

theorem inequalities_189979 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Real.sqrt ((a + c) * (b + d)) ≥ Real.sqrt (a * b) + Real.sqrt (c * d) := by 
  have h1 : 0 < (a + c) * (b + d) := by positivity
  have h2 : Real.sqrt ((a + c) * (b + d)) ^ 2 = (a + c) * (b + d) := by 
    rw [Real.sq_sqrt]
    positivity
  have h3 : Real.sqrt (a * b) ^ 2 = a * b := by 
    rw [Real.sq_sqrt]
    positivity
  have h4 : Real.sqrt (c * d) ^ 2 = c * d := by 
    rw [Real.sq_sqrt]
    positivity
  have h5 : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 = Real.sqrt (a * b) ^ 2 + Real.sqrt (c * d) ^ 2 + 2 * (Real.sqrt (a * b) * Real.sqrt (c * d)) := by
    ring 
  have h6 : Real.sqrt (a * b) ^ 2 = a * b := by
    rw [Real.sq_sqrt]
    positivity
  have h7 : Real.sqrt (c * d) ^ 2 = c * d := by 
    rw [Real.sq_sqrt]
    positivity
  have h8 : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 = a * b + c * d + 2 * (Real.sqrt (a * b) * Real.sqrt (c * d)) := by 
    rw [h5]
    rw [h6, h7]
  have h9 : Real.sqrt ((a + c) * (b + d)) ^ 2 ≥ (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 := by
    rw [h2, h8]
    have h11 : Real.sqrt ((a * b) * (c * d)) = Real.sqrt (a) * Real.sqrt (b) * Real.sqrt (c) * Real.sqrt (d) := by
      have h81 : Real.sqrt (a * b) * Real.sqrt (c * d) = Real.sqrt ((a * b) * (c * d)) := by
        have h11 : 0 ≤ a * b := by positivity
        have h12 : 0 ≤ c * d := by positivity
        have h13 : Real.sqrt ((a * b) * (c * d)) = Real.sqrt (a * b) * Real.sqrt (c * d) := by
          rw [Real.sqrt_mul (by positivity)]
        nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d)]
      have h82 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
        rw [Real.sqrt_mul (by positivity)]
      have h83 : Real.sqrt (c * d) = Real.sqrt c * Real.sqrt d := by
        rw [Real.sqrt_mul (by positivity)]
      have h84 : Real.sqrt (a * b) * Real.sqrt (c * d) =
          (Real.sqrt a * Real.sqrt b) * (Real.sqrt c * Real.sqrt d) := by
        rw [h82, h83]
      have h85 : Real.sqrt ((a * b) * (c * d)) = (Real.sqrt a * Real.sqrt b) * (Real.sqrt c * Real.sqrt d) := by 
        have h81' : Real.sqrt ((a * b) * (c * d)) = Real.sqrt (a * b) * Real.sqrt (c * d) := by
          rw [Real.sqrt_mul (by positivity)]
        rw [h81', h84]
      linarith [h85]
    nlinarith [mul_nonneg (show 0 ≤ (a : ℝ) by linarith) (show 0 ≤ (c : ℝ) by linarith), 
        mul_nonneg (show 0 ≤ (b : ℝ) by linarith) (show 0 ≤ (d : ℝ) by linarith),
        sq_nonneg (a * d - b * c), 
        sq_nonneg (a - c), 
        sq_nonneg (b - d), 
        mul_pos ha hb, 
        mul_pos ha hc, 
        mul_pos ha hd, 
        mul_pos hb hc, 
        mul_pos hb hd, 
        mul_pos hc hd, 
        Real.sqrt_nonneg (a), 
        Real.sqrt_nonneg (b), 
        Real.sqrt_nonneg (c), 
        Real.sqrt_nonneg (d), 
        Real.sq_sqrt (show 0 ≤ (a : ℝ) by positivity), 
        Real.sq_sqrt (show 0 ≤ (b : ℝ) by positivity), 
        Real.sq_sqrt (show 0 ≤ (c : ℝ) by positivity), 
        Real.sq_sqrt (show 0 ≤ (d : ℝ) by positivity), 
        sq_nonneg (Real.sqrt a * Real.sqrt d - Real.sqrt b * Real.sqrt c)
      ]
  have h10 : Real.sqrt ((a + c) * (b + d)) ≥ 0 := by positivity
  have h11 : Real.sqrt (a * b) + Real.sqrt (c * d) ≥ 0 := by
    have h9 : Real.sqrt (a * b) ≥ 0 := by positivity
    have h10 : Real.sqrt (c * d) ≥ 0 := by positivity
    linarith
  nlinarith [Real.sqrt_nonneg ((a + c) * (b + d)), Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), h9]