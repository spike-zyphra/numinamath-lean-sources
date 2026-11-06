import Mathlib

theorem algebra_13429 (k : ℝ) (hk : k^9 = 68719476736) : k = 16 := by
  have h2 : k ^ 9 = (16 : ℝ) ^ 9 := by 
    norm_num at hk ⊢
    linarith
  have h1 : k = (16 : ℝ) := by
    have h3 : k ^ 9 - (16 : ℝ) ^ 9 = 0 := by linarith
    have h4 : (k - (16 : ℝ)) * (k ^ 8 + k ^ 7 * 16 + k ^ 6 * (16 : ℝ) ^ 2 + k ^ 5 * (16 : ℝ) ^ 3 + k ^ 4 * (16 : ℝ) ^ 4 + k ^ 3 * (16 : ℝ) ^ 5 + k ^ 2 * (16 : ℝ) ^ 6 + k * (16 : ℝ) ^ 7 + (16 : ℝ) ^ 8) = 0 := by
      ring_nf at h3 ⊢
      <;> nlinarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · 
      linarith
    · 
      nlinarith [sq_nonneg (k ^ 4 - (16 : ℝ) ^ 4), sq_nonneg (k ^ 3 - (16 : ℝ) ^ 3), sq_nonneg (k ^ 2 - (16 : ℝ) ^ 2), sq_nonneg (k - (16 : ℝ)), sq_nonneg (k + (16 : ℝ)), sq_nonneg ((k ^ 2 - (16 : ℝ) ^ 2) / 2), sq_nonneg ((k ^ 3 * (16 : ℝ) / 2) ), sq_nonneg ((k ^ 4 * (16 : ℝ) / 2 ) ) ]
  linarith