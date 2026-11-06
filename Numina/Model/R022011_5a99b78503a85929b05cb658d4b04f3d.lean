import Mathlib

theorem algebra_223012 (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) + Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = 1 ↔
    5 ≤ x ∧ x ≤ 10 := by
  constructor
  · -- Forward: if the equation holds, then 5 ≤ x ∧ x ≤ 10
    intro h_eq
    have h1 : Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) = abs (Real.sqrt (x - 1) - 2) := by
      have h2 : x + 3 - 4 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
      rw [h2]
      have h3 : Real.sqrt ((Real.sqrt (x - 1) - 2) ^ 2) = abs (Real.sqrt (x - 1) - 2) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h3
    have h4 : Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = abs (Real.sqrt (x - 1) - 3) := by
      have h5 : x + 8 - 6 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 3) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
      rw [h5]
      have h6 : Real.sqrt ((Real.sqrt (x - 1) - 3) ^ 2) = abs (Real.sqrt (x - 1) - 3) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h6
    rw [h1, h4] at h_eq
    have h2 : 0 ≤ Real.sqrt (x - 1) := Real.sqrt_nonneg (x - 1)
    by_cases h3 : Real.sqrt (x - 1) ≥ 3
    · -- Case where sqrt(x - 1) ≥ 3
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h_eq
      have h4 : Real.sqrt (x - 1) = 3 := by nlinarith
      have h5 : x - 1 = 9 := by
        calc
          x - 1 = (Real.sqrt (x - 1)) ^ 2 := by rw [Real.sq_sqrt (by linarith)]
          _ = (3) ^ 2 := by rw [h4]
          _ = (9 : ℝ) := by norm_num
      constructor
      · nlinarith
      · nlinarith
    · -- Case sqrt(x - 1) < 3
      by_cases h4 : Real.sqrt (x - 1) ≥ 2
      · -- Case 2 ≤ sqrt(x - 1) < 3
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h_eq
        have h5 : 4 ≤ x - 1 := by
          nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
        have h6 : x - 1 ≤ 9 := by
          nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
        constructor
        · nlinarith
        · nlinarith
      · -- Case sqrt(x - 1) < 2
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h_eq
        have h4 : Real.sqrt (x - 1) = 2 := by nlinarith
        have h5 : x - 1 = 4 := by
          calc
            x - 1 = (Real.sqrt (x - 1)) ^ 2 := by rw [Real.sq_sqrt (by linarith)]
            _ = (2) ^ 2 := by rw [h4]
            _ = (4 : ℝ) := by norm_num
        constructor
        · nlinarith
        · nlinarith
  · -- Backward: if 5 ≤ x ∧ x ≤ 10, then the equation holds
    rintro ⟨hx1, hx2⟩
    have h1 : Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) = abs (Real.sqrt (x - 1) - 2) := by
      have h2 : x + 3 - 4 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
      rw [h2]
      have h3 : Real.sqrt ((Real.sqrt (x - 1) - 2) ^ 2) = abs (Real.sqrt (x - 1) - 2) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h3
    have h4 : Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = abs (Real.sqrt (x - 1) - 3) := by
      have h5 : x + 8 - 6 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 3) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
      rw [h5]
      have h6 : Real.sqrt ((Real.sqrt (x - 1) - 3) ^ 2) = abs (Real.sqrt (x - 1) - 3) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h6
    rw [h1, h4]
    have h2 : 2 ≤ Real.sqrt (x - 1) := by
      have h3 : 4 ≤ x - 1 := by linarith
      have h5 : Real.sqrt (x - 1) ≥ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h6 : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith
    have h3 : Real.sqrt (x - 1) ≤ 3 := by
      have h4 : x - 1 ≤ 9 := by linarith
      have h5 : Real.sqrt (x - 1) ≤ Real.sqrt (9 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h6 : Real.sqrt (9 : ℝ) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]