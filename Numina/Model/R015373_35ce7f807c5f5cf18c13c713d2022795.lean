import Mathlib

open Real

theorem inequalities_327970 {a : ℝ} (ha : a > 3) :
    3 * sqrt (a - 1) + sqrt (a - 3) < sqrt a + 3 * sqrt (a - 2) := by

  have h1 : 0 ≤ a - 3 := by linarith
  have h2 : 0 ≤ a - 2 := by linarith
  have h3 : 0 ≤ a - 1 := by linarith
  have h4 : 0 ≤ a := by linarith

  have h11 : sqrt (a - 1) ≥ 0 := Real.sqrt_nonneg (a - 1)
  have h12 : sqrt (a - 3) ≥ 0 := Real.sqrt_nonneg (a - 3)
  have h13 : sqrt (a) ≥ 0 := Real.sqrt_nonneg (a)
  have h14 : sqrt (a - 2) ≥ 0 := Real.sqrt_nonneg (a - 2)

  have h5 : (3 * sqrt (a - 1) + sqrt (a - 3)) ^ 2 < (sqrt a + 3 * sqrt (a - 2)) ^ 2 := by
    have h6 : (sqrt (a - 1)) ^ 2 = a - 1 := Real.sq_sqrt (by linarith)
    have h7 : (sqrt (a - 3)) ^ 2 = a - 3 := Real.sq_sqrt (by linarith)
    have h8 : (sqrt (a - 2)) ^ 2 = a - 2 := Real.sq_sqrt (by linarith)
    have h9 : (sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)

    have h13 : sqrt (a - 1) * sqrt (a - 3) = sqrt ((a - 1) * (a - 3)) := by
      rw [← Real.sqrt_mul (by linarith)]
    have h14 : sqrt a * sqrt (a - 2) = sqrt (a * (a - 2)) := by
      rw [← Real.sqrt_mul (by nlinarith)]
    
    have h20 : sqrt a * sqrt (a - 2) > sqrt (a - 1) * sqrt (a - 3) + 1 := by
      have h21 : sqrt a * sqrt (a - 2) = sqrt (a * (a - 2)) := h14
      have h22 : sqrt (a - 1) * sqrt (a - 3) = sqrt ((a - 1) * (a - 3)) := h13
      have h23 : (sqrt a * sqrt (a - 2)) ^ 2 > (sqrt (a - 1) * sqrt (a - 3) + 1) ^ 2 := by
        rw [h21, h22]
        have h24 : (sqrt (a * (a - 2))) ^ 2 = a * (a - 2) := by
          rw [Real.sq_sqrt]
          nlinarith
        have h25 : (sqrt ((a - 1) * (a - 3))) ^ 2 = (a - 1) * (a - 3) := by
          rw [Real.sq_sqrt]
          nlinarith
        have h30 : (sqrt (a * (a - 2))) ^ 2 > (sqrt ((a - 1) * (a - 3)) + 1) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (a * (a - 2)), Real.sqrt_nonneg ((a - 1) * (a - 3)), sq_nonneg (sqrt (a * (a - 2)) - sqrt ((a - 1) * (a - 3))), sq_nonneg (sqrt ((a - 1) * (a - 3))), sq_nonneg (sqrt (a * (a - 2))), Real.sq_sqrt (show (0 : ℝ) ≤ (a * (a - 2) : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ ((a - 1) * (a - 3) : ℝ) by nlinarith), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg (a - 2)), mul_nonneg (Real.sqrt_nonneg (a - 1)) (Real.sqrt_nonneg (a - 3)), sq_nonneg (a * (a - 2) - (a - 1) * (a - 3)), sq_nonneg (a - 2)
          ]
        linarith [h24, h25, h30]
      have h31 : sqrt a * sqrt (a - 2) ≥ 0 := by nlinarith [h13, Real.sqrt_nonneg (a - 2)]
      have h32 : sqrt (a - 1) * sqrt (a - 3) + 1 ≥ 0 := by nlinarith [h11, h12]
      nlinarith [h23, Real.sqrt_nonneg (a * (a - 2)), Real.sqrt_nonneg ((a - 1) * (a - 3)), Real.sqrt_nonneg (a - 1), Real.sqrt_nonneg (a - 3), Real.sqrt_nonneg a, Real.sqrt_nonneg (a - 2)]
    
    have h25 : 9 * (a - 1) + 6 * (sqrt (a - 1) * sqrt (a - 3)) + (a - 3) < a + 6 * (sqrt a * sqrt (a - 2)) + 9 * (a - 2) := by
      nlinarith [Real.sqrt_nonneg (a - 1), Real.sqrt_nonneg (a - 3), Real.sqrt_nonneg a, Real.sqrt_nonneg (a - 2), sq_nonneg (sqrt (a - 1) - sqrt (a - 3)), sq_nonneg (sqrt a - sqrt (a - 2)), mul_nonneg (Real.sqrt_nonneg (a - 1)) (Real.sqrt_nonneg (a - 3)), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg (a - 2)), h20, h11, h12, h13, h14]
    have h26 : (3 * sqrt (a - 1) + sqrt (a - 3)) ^ 2 = 9 * (a - 1) + 6 * (sqrt (a - 1) * sqrt (a - 3)) + (a - 3) := by
      calc
        (3 * sqrt (a - 1) + sqrt (a - 3)) ^ 2
          = 9 * ((sqrt (a - 1)) ^ 2) + 6 * (sqrt (a - 1) * sqrt (a - 3)) + ((sqrt (a - 3)) ^ 2) := by ring
        _ = 9 * (a - 1) + 6 * (sqrt (a - 1) * sqrt (a - 3)) + (a - 3) := by rw [h6, h7]
    have h27 : (sqrt a + 3 * sqrt (a - 2)) ^ 2 = a + 6 * (sqrt a * sqrt (a - 2)) + 9 * (a - 2) := by
      calc
        (sqrt a + 3 * sqrt (a - 2)) ^ 2
          = ((sqrt a) ^ 2) + 6 * (sqrt a * sqrt (a - 2)) + 9 * ((sqrt (a - 2)) ^ 2) := by ring
        _ = a + 6 * (sqrt a * sqrt (a - 2)) + 9 * (a - 2) := by rw [h9, h8]
    linarith [h25, h26, h27]

  have h6 : 0 ≤ (3 * sqrt (a - 1) + sqrt (a - 3) : ℝ) := by
    positivity
  have h7 : 0 ≤ (sqrt a + 3 * sqrt (a - 2) : ℝ) := by
    positivity
  nlinarith [h5, h6, h7, Real.sqrt_nonneg (a - 1), Real.sqrt_nonneg (a - 3), Real.sqrt_nonneg a, Real.sqrt_nonneg (a - 2)]