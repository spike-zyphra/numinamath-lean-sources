import Mathlib

open Real

theorem algebra_179442 {a : ℝ} (ha : 1 < a) (x : ℝ) (hx : 1 < x ∧ x < a) :
    logb a (logb a x) < (logb a x) ^ 2 ∧ (logb a x) ^ 2 < logb a (x ^ 2) := by
  have hx1 : 1 < x := hx.1
  have hx2 : x < a := hx.2
  have h0 : 0 < logb a x := by
    apply logb_pos
    all_goals
      linarith
  have h1 : logb a x < 1 := by
    have h2 : logb a x < logb a a := by
      apply Real.logb_lt_logb
      all_goals
        linarith
    have h3 : logb a a = 1 := by
      rw [logb_self_eq_one]
      linarith
    linarith
  have h3 : logb a (logb a x) < (logb a x) ^ 2 := by
    have h4 : logb a (logb a x) < 0 := by
      have h5 : logb a (logb a x) < logb a 1 := by
        apply Real.logb_lt_logb
        all_goals
          all_goals
            nlinarith
      have h7 : logb a 1 = 0 := by
        simp [logb_one]
      linarith
    have h4' : (logb a x) ^ 2 > (0 : ℝ) := by
      nlinarith [h0]
    linarith
  have h4 : (logb a x) ^ 2 < logb a (x ^ 2) := by
    have h9 : logb a (x ^ 2) = 2 * logb a x := by
      simp [logb_pow]
    nlinarith
  constructor <;> try linarith