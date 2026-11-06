import Mathlib

theorem inequalities_602423 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a^2 + 1) + Real.sqrt (b^2 + 1) < 1 + Real.sqrt ((a + b)^2 + 1) := by 
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : Real.sqrt (a^2 + 1) ≥ 0 := by positivity
  have h4 : Real.sqrt (b^2 + 1) ≥ 0 := by positivity
  have h5 : Real.sqrt ((a + b) ^ 2 + 1) ≥ 0 := by positivity
  suffices h : (Real.sqrt (a ^ 2 + 1) + Real.sqrt (b ^ 2 + 1)) ^ 2 < (1 + Real.sqrt ((a + b) ^ 2 + 1)) ^ 2 by
    nlinarith [Real.sqrt_nonneg (a ^ 2 + 1), Real.sqrt_nonneg (b ^ 2 + 1), Real.sqrt_nonneg ((a + b) ^ 2 + 1)]
  have h6 : (Real.sqrt (a ^ 2 + 1) + Real.sqrt (b ^ 2 + 1)) ^ 2 = Real.sqrt (a ^ 2 + 1) ^ 2 + Real.sqrt (b ^ 2 + 1) ^ 2 + 2 * (Real.sqrt (a ^ 2 + 1) * Real.sqrt (b ^ 2 + 1)) := by
    ring
  have h7 : (1 + Real.sqrt ((a + b) ^ 2 + 1)) ^ 2 = 1 + 2 * Real.sqrt ((a + b) ^ 2 + 1) + Real.sqrt ((a + b) ^ 2 + 1) ^ 2 := by
    ring
  have h8 : Real.sqrt (a ^ 2 + 1) ^ 2 = a^2 + 1 := by
    rw [Real.sq_sqrt]
    positivity
  have h9 : Real.sqrt (b ^ 2 + 1) ^ 2 = b^2 + 1 := by
    rw [Real.sq_sqrt]
    positivity
  have h10 : Real.sqrt ((a + b) ^ 2 + 1) ^ 2 = (a + b) ^ 2 + 1 := by
    rw [Real.sq_sqrt]
    positivity
  rw [h6, h8, h9, h7, h10]
  have h11 : Real.sqrt (a ^ 2 + 1) * Real.sqrt (b ^ 2 + 1) = Real.sqrt ((a ^ 2 + 1) * (b ^ 2 + 1)) := by
    rw [← Real.sqrt_mul (by positivity)]
  have h12 : Real.sqrt ((a ^ 2 + 1) * (b ^ 2 + 1)) < a * b + Real.sqrt ((a + b) ^ 2 + 1) := by
    have h13 : (Real.sqrt ((a ^ 2 + 1) * (b ^ 2 + 1))) ^ 2 < (a * b + Real.sqrt ((a + b) ^ 2 + 1)) ^ 2 := by
      have h14 : (Real.sqrt ((a ^ 2 + 1) * (b ^ 2 + 1))) ^ 2 = (a ^ 2 + 1) * (b ^ 2 + 1) := by 
        rw [Real.sq_sqrt]
        positivity
      have h15 : (a * b + Real.sqrt ((a + b) ^ 2 + 1)) ^ 2 = (a * b) ^ 2 + 2 * (a * b) * Real.sqrt ((a + b) ^ 2 + 1) + (Real.sqrt ((a + b) ^ 2 + 1)) ^ 2 := by
        ring
      have h16 : (Real.sqrt ((a + b) ^ 2 + 1)) ^ 2 = (a + b) ^ 2 + 1 := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [Real.sqrt_nonneg ((a ^ 2 + 1) * (b ^ 2 + 1)), Real.sqrt_nonneg ((a + b) ^ 2 + 1), 
                sq_nonneg (a * b - a * b), sq_nonneg ((a + b) ^ 2 + 1 - (a * b) ^ 2), Real.sq_sqrt (show 0 ≤ (a ^ 2 + 1) * (b ^ 2 + 1) by positivity), 
                mul_pos ha hb, sq_nonneg (a - b), sq_nonneg (a), sq_nonneg (b)
              ]
    have h14 : Real.sqrt ((a ^ 2 + 1) * (b ^ 2 + 1)) = Real.sqrt ((a ^ 2 + 1) * (b ^ 2 + 1)) := by rfl
    nlinarith [Real.sqrt_nonneg ((a ^ 2 + 1) * (b ^ 2 + 1)), Real.sqrt_nonneg ((a + b) ^ 2 + 1), 
          sq_nonneg (Real.sqrt ((a ^ 2 + 1) * (b ^ 2 + 1)) - (a * b + Real.sqrt ((a + b) ^ 2 + 1))), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + 1) * (b ^ 2 + 1) by positivity)
        ]
  nlinarith [Real.sqrt_nonneg (a ^ 2 + 1), Real.sqrt_nonneg (b ^ 2 + 1), Real.sqrt_nonneg ((a + b) ^ 2 + 1), 
        mul_nonneg (Real.sqrt_nonneg (a ^ 2 + 1)) (Real.sqrt_nonneg (b ^ 2 + 1)), 
        h11, h12, Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + 1) * (b ^ 2 + 1) by positivity)
      ]