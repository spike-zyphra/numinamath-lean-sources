import Mathlib

open Real

theorem inequalities_104303 (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    x * (sqrt (y - 1) + sqrt (z - 1)) + y * (sqrt (z - 1) + sqrt (x - 1)) +
    z * (sqrt (x - 1) + sqrt (y - 1)) ≤ x ^ 2 + y ^ 2 + z ^ 2 := by

  have h1 : sqrt (y - 1) ≤ (y) / 2 := by
    have h11 : 0 ≤ y - 1 := by linarith
    have h12 : (sqrt (y - 1) ) ^ 2 = y - 1 := Real.sq_sqrt h11
    have h13 : (y / 2) ^ 2 ≥ y - 1 := by
      nlinarith [sq_nonneg (y - 2)]
    have h14 : sqrt (y - 1) ≥ 0 := Real.sqrt_nonneg (y - 1)
    nlinarith [Real.sqrt_nonneg (y - 1), h12, h13]

  have h2 : sqrt (z - 1) ≤ (z) / 2 := by
    have h21 : 0 ≤ z - 1 := by linarith
    have h22 : (sqrt (z - 1) ) ^ 2 = z - 1 := Real.sq_sqrt h21
    have h23 : (z / 2) ^ 2 ≥ z - 1 := by
      nlinarith [sq_nonneg (z - 2)]
    have h24 : sqrt (z - 1) ≥ 0 := Real.sqrt_nonneg (z - 1)
    nlinarith [Real.sqrt_nonneg (z - 1), h22, h23]

  have h3 : sqrt (x - 1) ≤ (x) / 2 := by
    have h31 : 0 ≤ x - 1 := by linarith
    have h32 : (sqrt (x - 1) ) ^ 2 = x - 1 := Real.sq_sqrt h31
    have h33 : (x / 2) ^ 2 ≥ x - 1 := by
      nlinarith [sq_nonneg (x - 2)]
    have h34 : sqrt (x - 1) ≥ 0 := Real.sqrt_nonneg (x - 1)
    nlinarith [Real.sqrt_nonneg (x - 1), h32, h33]

  have h4 : x * (sqrt (y - 1) + sqrt (z - 1)) ≤ x * ( (y) / 2 + (z) / 2 ) := by
    have h5 : sqrt (y - 1) ≤ (y) / 2 := h1
    have h6 : sqrt (z - 1) ≤ (z) / 2 := h2
    have h7 : sqrt (y - 1) + sqrt (z - 1) ≤ (y) / 2 + (z) / 2 := by linarith [h5, h6]
    nlinarith [h7, mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ (1 : ℝ) by linarith)]

  have h5 : y * (sqrt (z - 1) + sqrt (x - 1)) ≤ y * ( (z) / 2 + (x) / 2 ) := by
    have h8 : sqrt (z - 1) ≤ (z) / 2 := h2
    have h9 : sqrt (x - 1) ≤ (x) / 2 := h3
    have h10 : sqrt (z - 1) + sqrt (x - 1) ≤ (z) / 2 + (x) / 2 := by linarith [h8, h9]
    nlinarith [h10, mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ (1 : ℝ) by linarith)]

  have h6 : z * (sqrt (x - 1) + sqrt (y - 1)) ≤ z * ( (x) / 2 + (y) / 2 ) := by
    have h11 : sqrt (x - 1) ≤ (x) / 2 := h3
    have h12 : sqrt (y - 1) ≤ (y) / 2 := h1
    have h13 : sqrt (x - 1) + sqrt (y - 1) ≤ (x) / 2 + (y) / 2 := by linarith [h11, h12]
    nlinarith [h13, mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ (1 : ℝ) by linarith)]

  have h7 : x * (sqrt (y - 1) + sqrt (z - 1)) + y * (sqrt (z - 1) + sqrt (x - 1)) +
      z * (sqrt (x - 1) + sqrt (y - 1)) ≤ x * ( (y) / 2 + (z) / 2 ) + y * ( (z) / 2 + (x) / 2 ) + z * ( (x) / 2 + (y) / 2 ) := by
    linarith [h4, h5, h6]

  have h8 : x * ( (y) / 2 + (z) / 2 ) + y * ( (z) / 2 + (x) / 2 ) + z * ( (x) / 2 + (y) / 2 ) ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith),
      mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith),
      mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ x by linarith)]

  linarith [h7, h8]