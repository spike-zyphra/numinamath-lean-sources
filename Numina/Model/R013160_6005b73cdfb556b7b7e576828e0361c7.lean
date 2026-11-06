import Mathlib

theorem algebra_129649 (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) + Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = 1 ↔
    5 ≤ x ∧ x ≤ 10 := by
  constructor
  · -- Assume the equation holds, prove 5 ≤ x ∧ x ≤ 10
    intro h_eq
    have h1 : 0 ≤ x - 1 := by linarith
    have h2 : Real.sqrt (x - 1) ≥ 0 := by apply Real.sqrt_nonneg
    have h3 : (x + 3 - 4 * Real.sqrt (x - 1)) = (Real.sqrt (x - 1) - 2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h4 : (x + 8 - 6 * Real.sqrt (x - 1)) = (Real.sqrt (x - 1) - 3) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h5 : Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) = |Real.sqrt (x - 1) - 2| := by
      rw [h3]
      have h6 : Real.sqrt ((Real.sqrt (x - 1) - 2) ^ 2) = |Real.sqrt (x - 1) - 2| := by
        rw [Real.sqrt_sq_eq_abs]
      linarith
    have h6 : Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = |Real.sqrt (x - 1) - 3| := by
      rw [h4]
      have h7 : Real.sqrt ((Real.sqrt (x - 1) - 3) ^ 2) = |Real.sqrt (x - 1) - 3| := by
        rw [Real.sqrt_sq_eq_abs]
      linarith
    rw [h5, h6] at h_eq
    have h7 : Real.sqrt (x - 1) ≥ 0 := Real.sqrt_nonneg (x - 1)
    have h8 : Real.sqrt (x - 1) ≥ 2 := by
      by_contra h
      push_neg at h
      have h10 : Real.sqrt (x - 1) < (2 : ℝ) := by linarith
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h_eq
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show x - 1 ≥ 0 by linarith)]
    have h9 : Real.sqrt (x - 1) ≤ 3 := by
      by_contra h
      push_neg at h
      have h10 : Real.sqrt (x - 1) > (3 : ℝ) := by linarith
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at h_eq
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show x - 1 ≥ 0 by linarith)]
    have h12 : x - 1 ≥ 4 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith), h8]
    have h13 : x - 1 ≤ 9 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith), h9]
    constructor
    · linarith
    · linarith
  · -- Assume 5 ≤ x ∧ x ≤ 10, prove the equation
    rintro ⟨h5, h10⟩
    have h1 : 0 ≤ x - 1 := by linarith
    have h2 : Real.sqrt (x - 1) ≥ 0 := by apply Real.sqrt_nonneg
    have h3 : (x + 3 - 4 * Real.sqrt (x - 1)) = (Real.sqrt (x - 1) - 2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h4 : (x + 8 - 6 * Real.sqrt (x - 1)) = (Real.sqrt (x - 1) - 3) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h5' : Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) = |Real.sqrt (x - 1) - 2| := by
      rw [h3]
      have h6 : Real.sqrt ((Real.sqrt (x - 1) - 2) ^ 2) = |Real.sqrt (x - 1) - 2| := by
        rw [Real.sqrt_sq_eq_abs]
      linarith
    have h6' : Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = |Real.sqrt (x - 1) - 3| := by
      rw [h4]
      have h7 : Real.sqrt ((Real.sqrt (x - 1) - 3) ^ 2) = |Real.sqrt (x - 1) - 3| := by
        rw [Real.sqrt_sq_eq_abs]
      linarith
    rw [h5', h6']
    have h7 : Real.sqrt (x - 1) ≥ (2 : ℝ) := by
      have h4' : Real.sqrt (x - 1) ≥ Real.sqrt (4 : ℝ) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      have h5' : Real.sqrt (4 : ℝ) = 2 := Real.sqrt_eq_cases.2 (by norm_num)
      linarith [h4', h5']
    have h8 : Real.sqrt (x - 1) ≤ (3 : ℝ) := by
      have h4' : Real.sqrt (x - 1) ≤ Real.sqrt (9 : ℝ) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      have h5' : Real.sqrt (9 : ℝ) = 3 := Real.sqrt_eq_cases.2 (by norm_num)
      linarith [h4', h5']
    have h9 : Real.sqrt (x - 1) - 2 ≥ 0 := by linarith [h7]
    have h10 : Real.sqrt (x - 1) - 3 ≤ 0 := by linarith [h8]
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]