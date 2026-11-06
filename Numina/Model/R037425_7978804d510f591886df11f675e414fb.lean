import Mathlib


lemma lemma_1 (x y z : ℝ) (h : x + y + z = 0) :
    27 * (x * y * z) ^ 2 ≤ -4 * (x * y + y * z + z * x) ^ 3 := by
  have h1 : z = -x - y := by
    linarith
  rw [h1]
  nlinarith [sq_nonneg (x * y - y * (-x - y) + (-x - y) * x), sq_nonneg (x + y + (-x - y)), sq_nonneg (x - y), sq_nonneg (y - (-x - y) ), sq_nonneg (x - (-x - y) ), sq_nonneg (x * y - y * (-x - y) ), sq_nonneg (y * (-x - y) - (-x - y) * x ), sq_nonneg ((x + y) * (y + (-x - y)) ), sq_nonneg ((y + (-x - y)) * (x + y) ), sq_nonneg ((x) * (y) - (y) * (-x - y) ), sq_nonneg ((y) * (-x - y) - (-x - y) * (x) ), sq_nonneg ((x) * (x) - (y) * (y) ), sq_nonneg ((x - y) * (x - (-x - y)) ), sq_nonneg ((y - (-x - y) ) * (y - (-x - y) ) ) ]


theorem inequalities_80552 (x y z : ℝ) (h : x + y + z = 0) :
    6 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≤ (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 := by
  have h1 : x ^ 3 + y ^ 3 + z ^ 3 = 3 * (x * y * z) := by
    have h2 : x + y + z = 0 := h
    have h3 : x ^ 3 + y ^ 3 + z ^ 3 - 3 * (x * y * z) = (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2 - (x * y + y * z + z * x)) := by 
      ring
    rw [show x + y + z = (0 : ℝ) by linarith] at h3
    linarith
  have h2 : x ^ 2 + y ^ 2 + z ^ 2 = -2 * (x * y + y * z + z * x) := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h3 : 27 * (x * y * z) ^ 2 ≤ -4 * (x * y + y * z + z * x) ^ 3 := lemma_1 x y z h
  have h4 : 6 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 = 54 * (x * y * z) ^ 2 := by
    rw [h1]
    nlinarith [sq_nonneg (3 * (x * y * z))]
  have h5 : (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 = -8 * (x * y + y * z + z * x) ^ 3 := by
    rw [h2]
    nlinarith [sq_nonneg (-2 * (x * y + y * z + z * x)), sq_nonneg ((x * y + y * z + z * x) ) ]
  nlinarith [sq_nonneg (x * y * z), sq_nonneg (x * y + y * z + z * x), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), h3, sq_nonneg (x * y * z), sq_nonneg (x * y + y * z + z * x) ]