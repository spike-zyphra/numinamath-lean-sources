import Mathlib

theorem algebra_313069 (x : ℝ) (hx : x ≥ 2010) :
    Real.sqrt (x - 2009 - 2 * Real.sqrt (x - 2010)) +
    Real.sqrt (x - 2009 + 2 * Real.sqrt (x - 2010)) = 2 ↔
    2010 ≤ x ∧ x ≤ 2011 := by
  constructor
  · -- Forward direction: if x ≥ 2010 and the equation holds, then 2010 ≤ x ≤ 2011
    intro h
    have h1 : x - 2009 - 2 * Real.sqrt (x - 2010) = (Real.sqrt (x - 2010) - 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 2010), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2010 by linarith)]
    have h2 : x - 2009 + 2 * Real.sqrt (x - 2010) = (Real.sqrt (x - 2010) + 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 2010), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2010 by linarith)]
    have h3 : Real.sqrt (x - 2009 - 2 * Real.sqrt (x - 2010)) =
        |Real.sqrt (x - 2010) - 1| := by
      rw [h1]
      have h4 : Real.sqrt ((Real.sqrt (x - 2010) - 1) ^ 2) = |Real.sqrt (x - 2010) - 1| := by
        rw [Real.sqrt_sq_eq_abs]
      exact h4
    have h4 : Real.sqrt (x - 2009 + 2 * Real.sqrt (x - 2010)) =
        |Real.sqrt (x - 2010) + 1| := by
      rw [h2]
      have h5 : Real.sqrt ((Real.sqrt (x - 2010) + 1) ^ 2) = |Real.sqrt (x - 2010) + 1| := by
        rw [Real.sqrt_sq_eq_abs]
      exact h5
    rw [h3, h4] at h
    have h5 : |Real.sqrt (x - 2010) + 1| = Real.sqrt (x - 2010) + 1 := by
      apply abs_of_nonneg
      linarith [Real.sqrt_nonneg (x - 2010)]
    rw [h5] at h
    by_cases h8 : Real.sqrt (x - 2010) ≥ 1
    · -- Case 1: sqrt(x - 2010) ≥ 1
      have h7 : |Real.sqrt (x - 2010) - 1| = Real.sqrt (x - 2010) - 1 := by
        rw [abs_of_nonneg (by nlinarith [h8, Real.sqrt_nonneg (x - 2010)])]
      rw [h7] at h
      have h8 : Real.sqrt (x - 2010) = 1 := by
        nlinarith
      have h9 : x - 2010 = 1 := by
        calc
          x - 2010 = (Real.sqrt (x - 2010)) ^ 2 := by
            rw [Real.sq_sqrt]
            linarith
          _ = (1) ^ 2 := by
            rw [h8]
          _ = (1 : ℝ) := by
            norm_num
      constructor
      · -- 2010 ≤ x
        linarith
      · -- x ≤ 2011
        linarith
    · -- Case 2: sqrt(x - 2010) < 1
      have h7 : |Real.sqrt (x - 2010) - 1| = 1 - Real.sqrt (x - 2010) := by
        rw [abs_of_neg (by
          nlinarith [Real.sqrt_nonneg (x - 2010), show Real.sqrt (x - 2010) < (1 : ℝ) by linarith]
        )]
        all_goals linarith [Real.sqrt_nonneg (x - 2010)]
      rw [h7] at h
      constructor
      · -- 2010 ≤ x
        linarith
      · -- x ≤ 2011
        nlinarith [Real.sqrt_nonneg (x - 2010), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2010 by linarith)]
  · -- Backward direction: if 2010 ≤ x ≤ 2011, then the equation holds
    rintro ⟨h10, h11⟩
    have h1 : x - 2009 - 2 * Real.sqrt (x - 2010) = (Real.sqrt (x - 2010) - 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 2010), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2010 by linarith)]
    have h2 : x - 2009 + 2 * Real.sqrt (x - 2010) = (Real.sqrt (x - 2010) + 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 2010), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2010 by linarith)]
    have h3 : Real.sqrt (x - 2009 - 2 * Real.sqrt (x - 2010)) =
        |Real.sqrt (x - 2010) - 1| := by
      rw [h1]
      have h4 : Real.sqrt ((Real.sqrt (x - 2010) - 1) ^ 2) = |Real.sqrt (x - 2010) - 1| := by
        rw [Real.sqrt_sq_eq_abs]
      exact h4
    have h4 : Real.sqrt (x - 2009 + 2 * Real.sqrt (x - 2010)) =
        |Real.sqrt (x - 2010) + 1| := by
      rw [h2]
      have h5 : Real.sqrt ((Real.sqrt (x - 2010) + 1) ^ 2) = |Real.sqrt (x - 2010) + 1| := by
        rw [Real.sqrt_sq_eq_abs]
      exact h5
    rw [h3, h4]
    have h5 : |Real.sqrt (x - 2010) + 1| = Real.sqrt (x - 2010) + 1 := by
      apply abs_of_nonneg
      linarith [Real.sqrt_nonneg (x - 2010)]
    have h6 : |Real.sqrt (x - 2010) - 1| = 1 - Real.sqrt (x - 2010) := by
      have h8 : Real.sqrt (x - 2010) ≤ (1 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (x - 2010), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2010 by linarith), show x - 2010 ≤ (1 : ℝ) by linarith]
      rw [abs_of_nonpos (by
        nlinarith [Real.sqrt_nonneg (x - 2010), h8]
      )]
      all_goals linarith [Real.sqrt_nonneg (x - 2010)]
    rw [h5, h6]
    all_goals linarith [Real.sqrt_nonneg (x - 2010)]