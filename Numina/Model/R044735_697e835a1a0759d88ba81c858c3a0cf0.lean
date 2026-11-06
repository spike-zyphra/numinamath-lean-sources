import Mathlib

open Real

theorem algebra_116021 {a : ℝ} (ha : 1 < a) (x : ℝ) (hx : 1 < x ∧ x < a) :
    logb a (logb a x) < (logb a x) ^ 2 ∧ (logb a x) ^ 2 < logb a (x ^ 2) := by
  have h1 : 0 < logb a x := by
    apply logb_pos
    all_goals
      try linarith
  have h2 : logb a x < 1 := by
    have h3 : logb a x < logb a a := by
      apply logb_lt_logb
      all_goals
        try linarith
    have h4 : logb a a = 1 := by
      rw [logb_self_eq_one]
      all_goals
        try linarith
    linarith [h3, h4]
  have h5 : logb a (logb a x) < (logb a x) ^ 2 := by
    have h7 : logb a (logb a x) < 0 := by
      have h8 : logb a (logb a x) < logb a 1 := by
        apply logb_lt_logb
        all_goals
          try linarith [h1]
      have h9 : logb a 1 = 0 := by
        simp [logb_one]
      linarith [h8, h9]
    have h10 : (logb a x) ^ 2 > 0 := by
      nlinarith
    linarith [h7, h10]
  have h6' : (logb a x) ^ 2 < logb a (x ^ 2) := by
    have h8 : logb a (x ^ 2) = 2 * logb a x := by
      simp [logb_pow]
    nlinarith [h1, h2]
  constructor
  · linarith [h5]
  · linarith [h6']