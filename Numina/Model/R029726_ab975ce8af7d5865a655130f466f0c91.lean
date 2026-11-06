import Mathlib

open Real Set

theorem algebra_283254 (a : ℝ) (b : ℝ) (hb : 0 < b) :
    (exp a - log b)^2 + (a - b)^2 ≥ 2 := by
  have h3 : (exp a - log b) ^ 2 + (a - b) ^ 2 - 2 ≥ 0 := by
    have h4 : exp a ≥ a + 1 := by
      linarith [Real.add_one_le_exp a, Real.exp_pos a]

    have h5 : log b ≤ b - 1 := by
      have h6 : log b ≤ b - 1 := by
        linarith [Real.log_le_sub_one_of_pos hb]
      linarith

    nlinarith [Real.exp_pos a, Real.log_pos (show 1 < b + 1 by linarith), sq_nonneg (exp a - (b)), sq_nonneg (log b - a), sq_nonneg (exp a - log b - (a - b)), sq_nonneg (exp a - a -1), sq_nonneg (log b - (b -1)), Real.exp_pos a, mul_pos (show 0 < b by linarith) (show 0 < b by linarith)]
  linarith