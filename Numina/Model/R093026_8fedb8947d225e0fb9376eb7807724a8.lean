import Mathlib

open Real

theorem algebra_265091 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : logb 2 a + logb 2 b ≥ 6) :
    a + b ≥ 16 := by
  have h1 : logb 2 a + logb 2 b = logb 2 (a * b) := by
    rw [logb_mul (by linarith) (by linarith)]
  have h2 : logb 2 (a * b) ≥ 6 := by linarith [h, h1]

  have h3 : a * b ≥ 64 := by
    by_contra h3
    push_neg at h3
    have h4 : logb 2 (a * b) < 6 := by
      have h5 : logb 2 (a * b) < logb 2 (64 : ℝ) := by
        apply (logb_lt_logb_iff (by norm_num) (by nlinarith) (by nlinarith)).mpr
        all_goals nlinarith
        all_goals linarith
      have h6 : logb 2 (64 : ℝ) = 6 := by
        rw [logb_eq_iff_rpow_eq] <;> (norm_num)
      linarith [h6, h5]
    linarith [h2, h4]

  nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 64),
          mul_pos ha hb, sq_nonneg (a - 8), sq_nonneg (b - 8)]