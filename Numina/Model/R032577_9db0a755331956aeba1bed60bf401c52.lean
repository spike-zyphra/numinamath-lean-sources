import Mathlib

open Real

theorem algebra_180196 {x : ℝ} (hx : 0 < x) :
    1/2 + logb 9 x - logb 3 (5 * x) > logb (1/3) (x + 3) := by
  have h1 : logb 9 x = logb 3 x / 2 := by
    have h2 : logb 9 x = logb 3 x / logb 3 (9 : ℝ) := by 
      field_simp [logb]
    have h3 : logb 3 (9 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h2, h3]
  have h2 : logb (1 / 3) (x + 3) = - logb 3 (x + 3) := by 
    have h3 : logb (1 / 3) (x + 3) = logb 3 (x + 3) / logb 3 (1 / 3 : ℝ) := by 
      field_simp [logb]
    have h4 : logb 3 (1 / 3 : ℝ) = -1 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h3, h4]
    <;> ring
  rw [h1, h2]
  have h3 : logb 3 (5 * x) = logb 3 5 + logb 3 x := by 
    rw [logb_mul (by norm_num) (by linarith)]
  rw [h3]
  have h4 : 1 / 2 + (logb 3 x / 2) - (logb 3 5 + logb 3 x) > - logb 3 (x + 3) := by
    have h5 : logb 3 (x + 3) > (logb 3 x / 2) + logb 3 5 - 1 / 2 := by
      have h6 : 2 * logb 3 (x + 3) > logb 3 x + 2 * logb 3 5 - 1 := by
        have h7 : 2 * logb 3 (x + 3) = logb 3 ((x + 3) ^ 2) := by
          simp [logb_pow]
        have h8 : logb 3 x + 2 * logb 3 5 - 1 = logb 3 ( (5 ^ 2 * x ) / 3 ) := by
          have h9 : logb 3 (5 ^ 2 * x) = logb 3 (5 ^ 2) + logb 3 x := by
            rw [logb_mul (by positivity) (by positivity)]
          have h10 : logb 3 (5 ^ 2) = 2 * logb 3 5 := by
            simp [logb_pow]
          have h11 : logb 3 ( (5 ^ 2 * x ) / 3 ) = logb 3 (5 ^ 2 * x) - logb 3 (3 : ℝ) := by
            rw [logb_div (by positivity) (by positivity)]
          have h12 : logb 3 (3 : ℝ) = 1 := by
            rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
          rw [h11, h9, h10, h12]
          <;> ring
        rw [h7, h8]
        have h9 : (x + 3) ^ 2 > (5 ^ 2 * x ) / 3 := by
          nlinarith [sq_nonneg (x - 7 / 6), sq_nonneg ((x + 3) * (3 : ℝ) - 25 / 2 * x), sq_nonneg (x + 3), sq_nonneg (x - 3), mul_pos hx (show (0 : ℝ) < 3 by norm_num)]
        have h10 : logb 3 ((x + 3) ^ 2) > logb 3 ( (5 ^ 2 * x ) / 3 ) := by
          apply Real.logb_lt_logb
          all_goals nlinarith [h9, mul_pos hx (show (0 : ℝ) < 3 by norm_num)]
        linarith
      linarith
    linarith
  linarith