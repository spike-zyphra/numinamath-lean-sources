import Mathlib

open Real

theorem algebra_603652 {f : ℝ → ℝ} (hf : ∀ x, f x = logb 2 (x + m)) (mpos : 0 < m)
    (has : 2 * f 2 = f 6 + f 0) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hgs : b ^ 2 = a * c) : f a + f c > 2 * f b := by

  have h3 : f a + f c = logb 2 ((a + m) * (c + m)) := by
    have h4 : f a + f c = logb 2 (a + m) + logb 2 (c + m) := by
      rw [hf a, hf c]
    have h5 : logb 2 (a + m) + logb 2 (c + m) = logb 2 ((a + m) * (c + m)) := by
      have h4' : 0 < a + m := by linarith
      have h5' : 0 < c + m := by linarith
      rw [← logb_mul (by linarith) (by linarith)]
      all_goals linarith
    linarith [h4, h5]

  have h4 : 2 * f b = 2 * logb 2 (b + m) := by
    rw [hf b]

  have h5 : (a + m) * (c + m) > (b + m) ^ 2 := by
    nlinarith [sq_pos_of_pos mpos, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_nonneg (a - c), sq_nonneg (b - m), sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h'
      apply habc.1
      linarith
    ), sq_pos_of_ne_zero (show a - c ≠ 0 by
      intro h'
      apply habc.2.1
      linarith
    ), sq_pos_of_ne_zero (show b - c ≠ 0 by
      intro h'
      apply habc.2.2
      linarith
    )]

  have h6 : logb 2 ((a + m) * (c + m)) > 2 * logb 2 (b + m) := by
    have h7 : 0 < (a + m) * (c + m) := by nlinarith
    have h8 : 0 < b + m := by nlinarith
    have h9 : logb 2 ((a + m) * (c + m)) > logb 2 ((b + m) ^ 2) := by
      apply Real.logb_lt_logb
      all_goals nlinarith [sq_pos_of_pos mpos, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, h5, sq_nonneg (b + m), sq_nonneg ((a + m) * (c + m)), sq_nonneg ((b + m) ^ 2)]
    have h10 : logb 2 ((b + m) ^ 2) = 2 * logb 2 (b + m) := by
      calc
        logb 2 ((b + m) ^ 2) = logb 2 ((b + m) ^ 2) := by rfl
        _ = 2 * logb 2 (b + m) := by simp [logb_pow]
    linarith [h9, h10]

  linarith [h3, h4, h6]