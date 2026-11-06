import Mathlib

open Real

theorem inequalities_294799 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    (a + b) / 2 > sqrt (a * b) ∧ sqrt (a * b) > 2 * a * b / (a + b) := by

  have h1 : (a + b) / 2 > sqrt (a * b) := by
    have h2 : (a + b) ^ 2 > 4 * (a * b) := by
      have h3 : (a - b) ^ 2 > 0 := by
        apply pow_two_pos_of_ne_zero
        intro h'
        apply hab
        linarith
      nlinarith
    have h3 : ( (a + b) / 2 ) ^ 2 > a * b := by
      nlinarith [h2]
    have h4 : (a + b) / 2 > 0 := by
      linarith [ha, hb]
    have h5 : sqrt (a * b) ≥ 0 := by positivity
    have h6 : ( (a + b) / 2 ) > sqrt (a * b) := by
      have h7 : ( (a + b) / 2 ) ^ 2 > (sqrt (a * b) ) ^ 2 := by
        have h8 : (sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (by positivity)
        nlinarith [h3, h8]
      nlinarith [h7, Real.sqrt_nonneg (a * b), show (0 : ℝ) < (a + b) / 2 by linarith [ha, hb]]
    linarith
  have h2 : sqrt (a * b) > 2 * a * b / (a + b) := by
    have h3 : 0 < a + b := by linarith
    have h8 : 2 * a * b / (a + b) < sqrt (a * b) := by
      apply (div_lt_iff₀ (by linarith)).mpr
      have h5 : sqrt (a * b) * (a + b) > 2 * a * b := by
        have h4 : sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (by positivity)
        have h7 : (a - b) ^ 2 > 0 := by
          apply pow_two_pos_of_ne_zero
          intro h'
          apply hab
          linarith
        nlinarith [h4, Real.sqrt_nonneg (a * b), sq_pos_of_ne_zero (show (a - b) ≠ 0 by
          intro h0
          apply hab
          linarith
        ), mul_pos ha hb, sq_nonneg (sqrt (a * b) ), sq_nonneg (a - b) ]
      linarith
    linarith
  constructor
  · exact h1
  · exact h2