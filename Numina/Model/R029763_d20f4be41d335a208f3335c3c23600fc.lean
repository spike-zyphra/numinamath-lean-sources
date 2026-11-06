import Mathlib

theorem inequalities_121674 {x y : ℝ} (hx : x ^ 5 > y ^ 4) (hy : y ^ 5 > x ^ 4) : x ^ 3 > y ^ 2 := by
  have hx11 : x > 0 := by 
    by_contra h 
    push_neg at h 
    have h1 : x ≤ 0 := by linarith 
    have h2 : x ^ 5 ≤ 0 := by 
      have h3 : x ≤ 0 := h1 
      have h4 : x ^ 2 ≥ 0 := by nlinarith 
      have h5 : x ^ 4 ≥ 0 := by nlinarith 
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 3), h3, sq_nonneg (x + 0), sq_nonneg (x - 0)]
    nlinarith [sq_nonneg (y ^ 2), sq_nonneg ((y ^ 2) ^ 2)]
  have hx12 : y > 0 := by 
    by_contra h 
    push_neg at h 
    have h1 : y ≤ 0 := by linarith 
    have h2 : y ^ 5 ≤ 0 := by 
      have h3 : y ≤ 0 := h1 
      have h4 : y ^ 2 ≥ 0 := by nlinarith 
      have h5 : y ^ 4 ≥ 0 := by nlinarith 
      nlinarith [sq_nonneg (y ^ 2), sq_nonneg (y ^ 3), h3, sq_nonneg (y + 0), sq_nonneg (y - 0)]
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg ((x ^ 2) ^ 2)]
  have hx13 : x ^ 3 > y ^ 2 := by 
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x ^ 2 - y * x), sq_nonneg (y ^ 2 - x * y), 
      pow_pos hx11 3, pow_pos hx11 4, pow_pos hx11 5, 
      pow_pos hx12 3, pow_pos hx12 4, pow_pos hx12 5, 
      mul_pos hx11 hx12, mul_pos hx11 (show 0 < y ^ 2 by positivity), 
      mul_pos hx12 (show 0 < x ^ 2 by positivity)]
  linarith [hx13]