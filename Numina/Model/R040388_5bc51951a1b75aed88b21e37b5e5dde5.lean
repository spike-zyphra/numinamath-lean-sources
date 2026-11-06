import Mathlib
theorem algebra_609070 (x y : ℝ) (h1 : x > y) (h2 : x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 + 2 * x * y = 40) (h3 : x * y + x + y = 8) : x = 3 + √7:= by
  have h4 : (x + y) ^ 2 + (x * y) ^ 2 = 40 := by
    nlinarith [h2]
  have h5 : x * y = 8 - (x + y) := by
    linarith [h3]
  have h7 : (x + y) ^ 2 + (8 - (x + y)) ^ 2 = 40 := by
    have heq1 : (x * y) = 8 - (x + y) := h5
    rw [heq1] at h4
    linarith
  have h8 : (x + y - 6) * (x + y - 2) = 0 := by
    nlinarith [h7]
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- case 1, x + y =6
    have h11 : x + y = 6 := by linarith
    have h12 : x * y = 2 := by
      have h13 : x * y = 8 - (x + y) := h5
      rw [h13]
      nlinarith [h11]
    have h10 : (x - (3 + Real.sqrt 7)) * (x - (3 - Real.sqrt 7)) = 0 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- x =3 + Real.sqrt 7
      have h14 : x = 3 + Real.sqrt 7 := by linarith
      linarith
    · -- x =3 - Real.sqrt 7
      have h15 : x = 3 - Real.sqrt 7 := by linarith
      -- This contradicts h1 as $3 - \sqrt{7} < 3 + \sqrt{7}$.
      have h16 : y = 3 + Real.sqrt 7 := by 
        nlinarith [ h15, Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num) ]
      nlinarith [ Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), h1 ]
  · -- case 2, x + y =2
    have h14 : x + y = 2 := by linarith
    have h15 : x * y = 6 := by
      have h16 : x * y = 8 - (x + y) := h5
      rw [h16]
      nlinarith [h14]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x * y - 6), sq_nonneg (x - y) ]