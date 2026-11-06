import Mathlib

theorem algebra_251517 (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) + Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = 1 ↔
    5 ≤ x ∧ x ≤ 10 := by 
  constructor
  · -- Assume equation hold
    intro h_eq
    have h1 : x - 1 ≥ 0 := by linarith 
    have h2 : x + 3 - 4 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 2) ^ 2 := by
      nlinarith [Real.sq_sqrt (show x - 1 ≥ 0 by linarith)]
    have h3 : x + 8 - 6 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 3) ^ 2 := by
      nlinarith [Real.sq_sqrt (show x - 1 ≥ 0 by linarith)]
    have eq1 : Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) = |Real.sqrt (x - 1) - 2| := by
      rw [h2]
      rw [Real.sqrt_sq_eq_abs]
    have eq2 : Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = |Real.sqrt (x - 1) - 3| := by
      rw [h3]
      rw [Real.sqrt_sq_eq_abs]
    rw [eq1, eq2] at h_eq
    have h4 : Real.sqrt (x - 1) ≥ 0 := by positivity
    -- Solve y equation 
    have h5 : 2 ≤ Real.sqrt (x - 1) ∧ Real.sqrt (x - 1) ≤ 3 := by 
      cases' abs_cases (Real.sqrt (x - 1) - 2) with h h <;> 
      cases' abs_cases (Real.sqrt (x - 1) - 3) with k k <;> 
      all_goals 
        constructor <;> nlinarith 
    have h6 : 4 ≤ x - 1 := by nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (x - 1) ≥ 0 by linarith), h5.1]
    have h7 : x - 1 ≤ 9 := by nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (x - 1) ≥ 0 by linarith), h5.2]
    constructor <;> linarith 
  · -- Assume 5 ≤ x ∧ x ≤ 10
    rintro ⟨h5, h10⟩
    have h1 : x - 1 ≥ 4 := by linarith 
    have h2 : x + 3 - 4 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 2) ^ 2 := by
      nlinarith [Real.sq_sqrt (show x - 1 ≥ 0 by linarith)]
    have h3 : x + 8 - 6 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 3) ^ 2 := by
      nlinarith [Real.sq_sqrt (show x - 1 ≥ 0 by linarith)]
    have eq1 : Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) = |Real.sqrt (x - 1) - 2| := by
      rw [h2]
      rw [Real.sqrt_sq_eq_abs]
    have eq2 : Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = |Real.sqrt (x - 1) - 3| := by
      rw [h3]
      rw [Real.sqrt_sq_eq_abs]
    rw [eq1, eq2]
    have h4 : 2 ≤ Real.sqrt (x - 1) := by 
      have h5' : x - 1 ≥ 4 := by linarith 
      have : Real.sqrt (x - 1) ≥ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h6 : Real.sqrt (4 : ℝ) = 2 := by 
        rw [Real.sqrt_eq_cases]
        norm_num
      linarith 
      all_goals linarith
    have h5 : Real.sqrt (x - 1) ≤ 3 := by 
      have h10' : x - 1 ≤ 9 := by linarith 
      have : Real.sqrt (x - 1) ≤ Real.sqrt (9 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h6 : Real.sqrt (9 : ℝ) = 3 := by 
        rw [Real.sqrt_eq_cases]
        norm_num
      linarith 
      all_goals linarith
    have h4' : Real.sqrt (x - 1) - 2 ≥ 0 := by linarith 
    have h5' : Real.sqrt (x - 1) - 3 ≤ 0 := by linarith 
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    nlinarith