import Mathlib

theorem inequalities_50339 (x y : ℝ) (hx : |x| < 1) (hy : |y| < 1) :
    |(x - y) / (1 - x * y)| < 1 := by
  have h1 : -1 < x := by linarith [abs_lt.mp hx]
  have h2 : x < 1 := by linarith [abs_lt.mp hx]
  have h3 : -1 < y := by linarith [abs_lt.mp hy]
  have h4 : y < 1 := by linarith [abs_lt.mp hy]

  have h7 : (x - y) ^ 2 < (1 - x * y) ^ 2 := by
    have h11 : x ^ 2 < 1 := by nlinarith [abs_lt.mp hx]
    have h12 : y ^ 2 < 1 := by nlinarith [abs_lt.mp hy]
    have h13 : x ^ 2 + y ^ 2 - (x * y) ^ 2 - 1 < 0 := by
      nlinarith [abs_lt.mp hx, abs_lt.mp hy, mul_pos (show 0 < 1 - x by nlinarith) (show 0 < 1 - y by nlinarith), sq_nonneg (x^2 -1), sq_nonneg (y^2 -1), mul_pos (show 0 < 1 - x^2 by nlinarith) (show 0 < 1 - y^2 by nlinarith)]
    nlinarith
  have h8 : 0 < 1 - x * y := by nlinarith

  have h10 : |x - y| < |1 - x * y| := by
    have h11 : (x - y) ^ 2 < (1 - x * y) ^ 2 := h7
    have h12 : |x - y| = Real.sqrt ((x - y) ^ 2) := by 
      rw [Real.sqrt_sq_eq_abs]
    have h13 : |1 - x * y| = Real.sqrt ((1 - x * y) ^ 2) := by 
      rw [Real.sqrt_sq_eq_abs]
    have h14 : Real.sqrt ((x - y) ^ 2) < Real.sqrt ((1 - x * y) ^ 2) := by 
      apply Real.sqrt_lt_sqrt
      all_goals nlinarith
    linarith [h12, h13, h14]

  have h9 : |(x - y) / (1 - x * y)| < 1 := by
    have h14 : |(x - y) / (1 - x * y)| = |x - y| / |1 - x * y| := by
      field_simp [abs_div]
    rw [h14]
    have h18 : |1 - x * y| > 0 := by
      have h16 : 0 < 1 - x * y := h8
      have h17 : |1 - x * y| > 0 := by
        apply abs_pos.mpr
        linarith
      assumption
    apply (div_lt_iff' (by linarith)).mpr
    linarith [h10]
  exact h9