import Mathlib

open Real

theorem inequalities_94553 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    (a + b) / 2 > sqrt (a * b) ∧ sqrt (a * b) > 2 * a * b / (a + b) := by

  have h1 : (a + b) / 2 > Real.sqrt (a * b) := by
    have h2 : (Real.sqrt (a * b)) ^ 2 = a * b := by
      rw [Real.sq_sqrt]
      nlinarith
    have h3 : ((a + b) / 2) ^ 2 > a * b := by
      nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
        intro h
        apply hne
        linarith
      ), mul_pos ha hb]
    have h4 : (Real.sqrt (a * b) ) ≥ 0 := by positivity
    have h5 : ((a + b) / 2) ^ 2 > (Real.sqrt (a * b) ) ^ 2 := by
      nlinarith [h2, h3]
    have h6 : (a + b) / 2 > Real.sqrt (a * b) := by
      nlinarith [Real.sqrt_nonneg (a * b), show 0 ≤ (a + b) / 2 by nlinarith]
    exact h6

  have h6 : Real.sqrt (a * b) > 2 * a * b / (a + b) := by
    have h7 : 0 < a * b := mul_pos ha hb
    have h8 : 0 < a + b := by linarith [ha, hb]
    have h9 : Real.sqrt (a * b) * (a + b) > 2 * a * b := by
      have h11 : (Real.sqrt (a * b) * (a + b)) ^ 2 > (2 * a * b) ^ 2 := by
        have h12 : (Real.sqrt (a * b) * (a + b)) ^ 2 = (Real.sqrt (a * b)) ^ 2 * (a + b) ^ 2 := by ring
        have h13 : (Real.sqrt (a * b)) ^ 2 = a * b := by
          rw [Real.sq_sqrt]
          nlinarith
        rw [h12, h13]
        have h14 : (2 * a * b) ^ 2 = 4 * (a * b) ^ 2 := by ring
        rw [h14]
        have h15 : a * b * (a + b) ^ 2 > 4 * (a * b) ^ 2 := by
          nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
            intro h
            apply hne
            linarith
          ), mul_pos ha hb]
        nlinarith [mul_pos ha hb]
      have h16 : (Real.sqrt (a * b) * (a + b) ) ≥ 0 := by
        have h17 : Real.sqrt (a * b) ≥ 0 := by positivity
        have h18 : (a + b) > 0 := by linarith [ha, hb]
        nlinarith [h17, h18]
      have h18 : (Real.sqrt (a * b) * (a + b) ) > 2 * a * b := by
        nlinarith [h11, mul_pos ha hb, Real.sqrt_nonneg (a * b), sq_nonneg (Real.sqrt (a * b) * (a + b) - (2 * a * b)), sq_pos_of_pos (show 0 < (a + b : ℝ) by linarith [ha, hb]), sq_nonneg (Real.sqrt (a * b) ^ 2 - (2 * a * b) ^ 2), mul_pos ha hb]
      exact h18
    have h10 : (2 * a * b / (a + b) ) < Real.sqrt (a * b) := by
      have h11 : 0 < (a + b : ℝ) := by linarith [ha, hb]
      apply (div_lt_iff₀ (by linarith)).mpr
      nlinarith [h9]
    linarith
  constructor
  · exact h1
  · exact h6