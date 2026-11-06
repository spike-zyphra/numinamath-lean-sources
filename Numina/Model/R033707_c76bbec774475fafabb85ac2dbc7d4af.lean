import Mathlib

theorem algebra_270900 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : 2 * x ^ 3 = 2 * y * (x ^ 2 + 1) - (z ^ 2 + 1)) (h2 : 2 * y ^ 4 = 3 * z * (y ^ 2 + 1) - 2 * (x ^ 2 + 1))
    (h3 : 2 * z ^ 5 = 4 * x * (z ^ 2 + 1) - 3 * (y ^ 2 + 1)) :
    x = 1 ∧ y = 1 ∧ z = 1 := by 
  have h4 : (x - 1) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg (z ^ 2 - 1),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have hx1 : x - 1 = 0 := by
    apply pow_eq_zero 
    exact h4

  have hx2 : x = 1 := by
    linarith
  
  have h5 : (y - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg (z ^ 2 - 1),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have hy1 : y - 1 = 0 := by
    apply pow_eq_zero 
    exact h5

  have hy2 : y = 1 := by
    linarith
  
  have h6 : (z - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg (z ^ 2 - 1),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have hz1 : z - 1 = 0 := by
    apply pow_eq_zero 
    exact h6

  have hz2 : z = 1 := by
    linarith
  
  constructor
  · exact hx2
  constructor
  · exact hy2
  · exact hz2