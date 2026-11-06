import Mathlib

theorem algebra_184309 (x : ℝ) (hx : x ^ 2 - 1 ≥ 0) :
    (4 * x * (x + Real.sqrt (x ^ 2 - 1)) ^ 2) / ((x + Real.sqrt (x ^ 2 - 1)) ^ 4 - 1) =
    1 / Real.sqrt (x ^ 2 - 1) := by 
  have h1 : Real.sqrt (x ^ 2 - 1) ≥ 0 := by
    apply Real.sqrt_nonneg
  by_cases h2 : x = 1
  · -- If x =1
    rw [h2]
    norm_num
    all_goals
      nlinarith [Real.sqrt_nonneg (0 : ℝ)]
  · -- x ≠1 case
    by_cases h2 : x = -1
    · -- If x =-1
      rw [h2]
      norm_num 
      all_goals
        nlinarith [Real.sqrt_nonneg (0 : ℝ)]
    · -- x ≠1, x ≠-1
      have h3 : x^2 - 1 > 0 := by
        by_contra h
        push_neg at h
        have h4 : x^2 -1 = 0 := by linarith
        have h5 : (x - 1) * (x + 1) = 0 := by nlinarith
        cases' (mul_eq_zero.mp h5) with h6 h7
        · -- Case x - 1=0
          have h8 : x = 1 := by linarith
          tauto 
        · -- Case x + 1=0 
          have h9 : x = -1 := by linarith
          exfalso 
          tauto
      have h2 : Real.sqrt (x ^ 2 - 1) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have h4 : (x + Real.sqrt (x^2 - 1))^2 = 2*x^2 + 2*x*Real.sqrt (x^2 -1) -1 := by
        nlinarith [Real.sqrt_nonneg (x^2 - 1), Real.sq_sqrt (show x^2 -1 ≥0 by linarith), mul_nonneg (Real.sqrt_nonneg (x^2-1)) (Real.sqrt_nonneg (x^2-1))]
      have h7 : 4 * x * (x + Real.sqrt (x^2 -1))^2 * Real.sqrt (x ^ 2 -1) = (x + Real.sqrt (x^2 -1))^4 -1 := by
        nlinarith [Real.sqrt_nonneg (x^2 -1), Real.sq_sqrt (show x^2-1 ≥ 0 by linarith), sq_nonneg (x - Real.sqrt (x^2-1)), sq_nonneg (x + Real.sqrt (x^2-1) - Real.sqrt (x^2-1)), sq_nonneg (x + Real.sqrt (x^2-1) + Real.sqrt (x^2-1)), sq_nonneg (Real.sqrt (x^2-1) -x), sq_nonneg (Real.sqrt (x^2-1) +x), h4]
      have eq' : (4 * x * (x + Real.sqrt (x ^ 2 - 1)) ^ 2) / ((x + Real.sqrt (x ^ 2 - 1)) ^ 4 - 1) =
          1 / Real.sqrt (x^2 -1) := by
        have hn1 : (x + Real.sqrt (x ^2 -1))^4 -1 ≠ 0 := by
          by_contra h
          have h8 : (x + Real.sqrt (x^2 -1))^4 -1 =0 := by linarith
          have h9 : 4 * x * (x + Real.sqrt (x^2 -1))^2 =0 := by
            nlinarith [Real.sqrt_nonneg (x^2 -1), Real.sq_sqrt (show x^2-1 ≥0 by linarith), sq_nonneg (x^2 -1), sq_nonneg (x ^2 - (x + Real.sqrt (x^2 -1))^2), h4, h8]
          have h10 : x =0 := by
            nlinarith [Real.sqrt_nonneg (x^2 -1), Real.sq_sqrt (show x^2-1 ≥0 by linarith), sq_nonneg (x ^2 -1), sq_nonneg (x^2 - (x + Real.sqrt (x^2 -1))^2), h4, h8]
          nlinarith [Real.sqrt_nonneg (x^2 -1), Real.sq_sqrt (show x^2-1 ≥0 by linarith), sq_nonneg (Real.sqrt (x^2 -1)), h10]
        have hn2 : Real.sqrt (x^2 -1) ≠ 0 := by nlinarith 
        have eq1 : (4 * x * (x + Real.sqrt (x^2 - 1)) ^ 2) / ((x + Real.sqrt (x^2 -1)) ^4 - 1) = 1 / Real.sqrt (x^2 -1) := by 
          field_simp [hn1, hn2]
          nlinarith [Real.sqrt_nonneg (x^2 -1), Real.sq_sqrt (show x^2-1 ≥0 by linarith), sq_nonneg (x^2 -1), sq_nonneg (x ^2 - (x + Real.sqrt (x^2 -1))^2), h4, h7, sq_nonneg ((x + Real.sqrt (x^2 -1))^2 -1)]
        assumption
      assumption