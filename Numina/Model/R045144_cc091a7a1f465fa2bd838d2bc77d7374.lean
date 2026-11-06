import Mathlib

open Real

theorem algebra_276291 (x : ℝ) (hx : x ≥ 1) :
    if x ≤ 2 then sqrt (x + 2 * sqrt (x - 1)) + sqrt (x - 2 * sqrt (x - 1)) = 2
    else sqrt (x + 2 * sqrt (x - 1)) + sqrt (x - 2 * sqrt (x - 1)) = 2 * sqrt (x - 1) := by

  by_cases h : x ≤ 2
  · -- Assume x ≤ 2
    have h1 : x - 1 ≤ 1 := by linarith
    have h3 : sqrt (x - 1) ≤ 1 := by
      have h4 : sqrt (x - 1) ≤ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h5 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith [h4, h5]

    have h_eq1 : sqrt (x + 2 * sqrt (x - 1)) = sqrt (x - 1) + 1 := by
      have h_eq2 : (sqrt (x - 1) + 1) ^ 2 = x + 2 * sqrt (x - 1) := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
      have h_eq3 : sqrt (x + 2 * sqrt (x - 1)) = sqrt (x - 1) + 1 := by
        rw [← h_eq2]
        field_simp [Real.sqrt_sq (show 0 ≤ sqrt (x - 1) + 1 by positivity)]
        all_goals linarith [Real.sqrt_nonneg (x - 1)]
      exact h_eq3

    have h_eq4 : sqrt (x - 2 * sqrt (x - 1)) = 1 - sqrt (x - 1) := by
      have h_eq5 : (x - 2 * sqrt (x - 1)) = (sqrt (x - 1) - 1) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
      have h_eq6 : sqrt (x - 2 * sqrt (x - 1)) = sqrt ((sqrt (x - 1) - 1) ^ 2) := by
        rw [h_eq5]
      have h_eq7 : sqrt ((sqrt (x - 1) - 1) ^ 2) = 1 - sqrt (x - 1) := by
        have h8 : sqrt ((sqrt (x - 1) - 1) ^ 2) = |sqrt (x - 1) - 1| := by
          rw [Real.sqrt_sq_eq_abs]
        rw [h8]
        have h9 : sqrt (x - 1) - 1 ≤ 0 := by linarith [h3]
        rw [abs_of_nonpos h9]
        all_goals linarith
      rw [h_eq6, h_eq7]

    rw [if_pos h]
    nlinarith [h_eq1, h_eq4, Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
  · -- Assume x > 2
    have h4 : x > 2 := by linarith
    have h5 : sqrt (x - 1) > 1 := by
      have h6 : Real.sqrt (x - 1) > Real.sqrt (1 : ℝ) := by
        apply Real.sqrt_lt_sqrt
        all_goals linarith
      have h10 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith [h6, h10]

    have h_eq1 : sqrt (x + 2 * sqrt (x - 1)) = sqrt (x - 1) + 1 := by
      have h_eq2 : (sqrt (x - 1) + 1) ^ 2 = x + 2 * sqrt (x - 1) := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
      have h_eq3 : sqrt (x + 2 * sqrt (x - 1)) = sqrt (x - 1) + 1 := by
        rw [← h_eq2]
        field_simp [Real.sqrt_sq (show 0 ≤ sqrt (x - 1) + 1 by positivity)]
        all_goals linarith [Real.sqrt_nonneg (x - 1)]
      exact h_eq3

    have h_eq4 : sqrt (x - 2 * sqrt (x - 1)) = sqrt (x - 1) - 1 := by
      have h_eq5 : (x - 2 * sqrt (x - 1)) = (sqrt (x - 1) - 1) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
      have h_eq6 : sqrt (x - 2 * sqrt (x - 1)) = sqrt ((sqrt (x - 1) - 1) ^ 2) := by
        rw [h_eq5]
      have h_eq7 : sqrt ((sqrt (x - 1) - 1) ^ 2) = sqrt (x - 1) - 1 := by
        have h8 : sqrt ((sqrt (x - 1) - 1) ^ 2) = |sqrt (x - 1) - 1| := by
          rw [Real.sqrt_sq_eq_abs]
        rw [h8]
        have h9 : sqrt (x - 1) - 1 > 0 := by linarith [h5]
        rw [abs_of_pos h9]
        all_goals linarith
      rw [h_eq6, h_eq7]

    rw [if_neg h]
    nlinarith [h_eq1, h_eq4, Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]