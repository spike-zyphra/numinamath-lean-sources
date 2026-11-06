import Mathlib


theorem algebra_280203 (a : ℝ) (ha : 0 < a ∧ a < 1) :
    ((Real.sqrt (1 + a)) / (Real.sqrt (1 + a) - Real.sqrt (1 - a)) +
     (1 - a) / (Real.sqrt (1 - a^2) - 1 + a)) *
    (Real.sqrt ((1 / a^2) - 1) - 1 / a) = -1 := by

  have ha1 : 0 < a := ha.1
  have ha2 : a < 1 := ha.2
  have ha3 : 0 < 1 - a := by linarith
  have ha4 : 0 < 1 + a := by linarith
  have ha5 : 0 < 1 - a^2 := by nlinarith

  have h1 : Real.sqrt (1 - a^2) = Real.sqrt (1 - a) * Real.sqrt (1 + a) := by
    have h2 : (1 - a^2 : ℝ) = (1 - a) * (1 + a) := by
      nlinarith
    rw [h2]
    have h3 : 0 ≤ (1 - a : ℝ) := by linarith
    have h4 : 0 ≤ (1 + a : ℝ) := by linarith
    rw [Real.sqrt_mul (by nlinarith)]

  have h2 : Real.sqrt (1 + a) / (Real.sqrt (1 + a) - Real.sqrt (1 - a)) = (1 + a + Real.sqrt (1 + a) * Real.sqrt (1 - a)) / (2 * a) := by
    have h3 : Real.sqrt (1 + a) - Real.sqrt (1 - a) ≠ 0 := by
      have h4 : Real.sqrt (1 + a) > Real.sqrt (1 - a) := by
        apply Real.sqrt_lt_sqrt
        all_goals nlinarith
      nlinarith
    field_simp [h3]
    nlinarith [Real.sqrt_nonneg (1 + a), Real.sqrt_nonneg (1 - a), Real.sq_sqrt (show 0 ≤ 1 + a by linarith), Real.sq_sqrt (show 0 ≤ 1 - a by linarith), sq_pos_of_pos ha1, sq_pos_of_pos ha3]
  
  have h3 : (1 - a) / (Real.sqrt (1 - a^2) - 1 + a) = (Real.sqrt (1 - a^2) + 1 - a) / (2 * a) := by
    have h4 : Real.sqrt (1 - a^2) - 1 + a ≠ 0 := by
      nlinarith [Real.sqrt_nonneg (1 - a^2), Real.sq_sqrt (show 0 ≤ (1 - a ^ 2 : ℝ) by nlinarith), sq_pos_of_pos ha1, sq_pos_of_pos ha3, sq_pos_of_pos ha4]
    field_simp [h4]
    have h5 : Real.sqrt (1 - a^2) ^ 2 = 1 - a^2 := by
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith [Real.sqrt_nonneg (1 - a^2), Real.sq_sqrt (show 0 ≤ 1 - a^2 by nlinarith), sq_pos_of_pos ha1, sq_pos_of_pos ha3, sq_pos_of_pos ha4]
  
  have h4 : Real.sqrt (1 + a) / (Real.sqrt (1 + a) - Real.sqrt (1 - a)) + (1 - a) / (Real.sqrt (1 - a^2) - 1 + a) = (1 + Real.sqrt (1 - a^2)) / a := by
    rw [h2, h3]
    have h5 : Real.sqrt (1 + a) * Real.sqrt (1 - a) = Real.sqrt (1 - a^2) := by
      have h12 : Real.sqrt (1 + a) * Real.sqrt (1 - a) = Real.sqrt ((1 + a) * (1 - a)) := by
        rw [← Real.sqrt_mul (by nlinarith)]
      have h13 : (1 + a) * (1 - a) = 1 - a^2 := by
        nlinarith
      rw [h13] at h12
      linarith [h12]
    rw [h5] at h2
    field_simp [show a ≠ 0 by linarith, show 1 - a ≠ 0 by linarith]
    nlinarith [Real.sqrt_nonneg (1 - a^2), Real.sq_sqrt (show 0 ≤ (1 - a^2 : ℝ) by nlinarith)]
  
  have h5 : Real.sqrt ((1 / a^2) - 1) = Real.sqrt (1 - a^2) / a := by
    have h6 : (1 / a^2) - 1 = (1 - a^2) / a^2 := by
      field_simp [show a ≠ 0 by linarith]
      <;> nlinarith
    rw [h6]
    have h7 : Real.sqrt ((1 - a^2) / a^2) = Real.sqrt (1 - a^2) / Real.sqrt (a^2) := by
      rw [Real.sqrt_div (by nlinarith)]
    rw [h7]
    have h8 : Real.sqrt (a^2) = a := by
      rw [Real.sqrt_sq (show 0 ≤ a by linarith)]
    rw [h8]

  have h6 : Real.sqrt ((1 / a^2) - 1) - 1 / a = (Real.sqrt (1 - a^2) - 1) / a := by
    rw [h5]
    field_simp [show a ≠ 0 by linarith]
    all_goals linarith

  rw [h4, h6]

  have h7 : Real.sqrt (1 - a^2) ^ 2 = 1 - a^2 := by
    rw [Real.sq_sqrt]
    nlinarith

  field_simp [show a ≠ 0 by linarith, h7]
  nlinarith [Real.sqrt_nonneg (1 - a^2), Real.sq_sqrt (show 0 ≤ 1 - a^2 by nlinarith), sq_pos_of_pos ha1, sq_pos_of_pos ha3]