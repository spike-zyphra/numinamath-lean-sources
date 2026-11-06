import Mathlib

open Real

theorem inequalities_82765 (a b : ℝ) (ha : 0 < b) (hb : b < a) :
    (a - b)^2 / (8 * a) < (a + b) / 2 - sqrt (a * b) ∧ (a + b) / 2 - sqrt (a * b) < (a - b)^2 / (8 * b) := by
  have ha1 : 0 < a := by linarith
  have ha2 : 0 < a * b := by nlinarith
  have h3 : sqrt (a * b) > 0 := by
    apply Real.sqrt_pos.2
    positivity

  constructor
  · -- Prove the first inequality: (a - b)^2 / (8 * a) < (a + b) / 2 - sqrt (a * b)
    have h4 : (a - b) ^ 2 / (8 * a) < (a + b) / 2 - sqrt (a * b) := by
      have h5 : 0 < (8 * a) := by
        nlinarith
      have h6 : (a - b) ^ 2 < 4 * a * (a + b) - 8 * a * sqrt (a * b) := by
        have h7 : (sqrt (a * b)) ^ 2 = a * b := by
          rw [Real.sq_sqrt]
          positivity
        have h11 : 0 < a - b := by linarith
        have h12 : (sqrt (a * b) ) ^ 2 = a * b := h7
        have h13 : (sqrt (a * b) ) > 0 := by positivity
        nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b), sq_nonneg (sqrt (a * b) - (a / 2)), sq_nonneg (sqrt (a * b) - (b / 2)), sq_nonneg (a - b - 2 * sqrt (a * b)), sq_nonneg (a + b - 2 * sqrt (a * b)), mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith), sq_pos_of_pos (show 0 < a - b by linarith), sq_nonneg ( (sqrt (a * b) ) ^ 2 - a * b ), sq_nonneg ((a - b) ^ 2 - 4 * (a * b) ) ]
      have h7 : (a - b) ^ 2 / (8 * a) < (a + b) / 2 - sqrt (a * b) := by
        have pos1 : (0 < 8 * a) := h5
        apply (div_lt_iff₀ (by linarith)).mpr
        linarith
      exact h7
    linarith
  · -- Prove the second inequality: (a + b) / 2 - sqrt (a * b) < (a - b)^2 / (8 * b)
    have h4 : (a + b) / 2 - sqrt (a * b) < (a - b) ^ 2 / (8 * b) := by
      have h5 : 0 < (8 * b) := by
        nlinarith
      have h7 : 4 * b * (a + b) - 8 * b * sqrt (a * b) < (a - b) ^ 2 := by
        have h7 : (sqrt (a * b)) ^ 2 = a * b := by
          rw [Real.sq_sqrt]
          positivity
        have h11 : 0 < a - b := by linarith
        have h12 : (sqrt (a * b) ) ^ 2 = a * b := h7
        have h13 : (sqrt (a * b) ) > 0 := by positivity
        nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b), sq_nonneg (sqrt (a * b) - (a / 2)), sq_nonneg (sqrt (a * b) - (b / 2)), sq_nonneg (a - b - 2 * sqrt (a * b)), sq_nonneg (a + b - 2 * sqrt (a * b)), mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith), sq_pos_of_pos (show 0 < a - b by linarith), sq_nonneg ( (sqrt (a * b) ) ^ 2 - a * b ), sq_nonneg ((a - b) ^ 2 - 4 * (a * b) ) ]
      have h3' : (a + b) / 2 - sqrt (a * b) < (a - b) ^ 2 / (8 * b) := by
        have pos1 : (0 < 8 * b) := h5
        apply (lt_div_iff₀ (by linarith)).mpr
        linarith
      exact h3'
    linarith