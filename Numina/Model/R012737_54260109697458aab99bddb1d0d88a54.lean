import Mathlib

theorem algebra_222972 (x : ℝ) (hx : x ≥ 1) :
    Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) +
    Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = 1 ↔ 5 ≤ x ∧ x ≤ 10 := by
  constructor
  · -- Assume the equation holds, prove 5 ≤ x ∧ x ≤ 10
    intro h_eq
    have h1 : x + 3 - 4 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h2 : x + 8 - 6 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 3) ^ 2 := by 
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h3 : Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) = abs (Real.sqrt (x - 1) - 2) := by 
      rw [h1]
      have h4 : Real.sqrt ((Real.sqrt (x - 1) - 2) ^ 2) = abs (Real.sqrt (x - 1) - 2) := by 
        rw [Real.sqrt_sq_eq_abs]
      exact h4
    have h5 : Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = abs (Real.sqrt (x - 1) - 3) := by 
      rw [h2]
      have h6 : Real.sqrt ((Real.sqrt (x - 1) - 3) ^ 2) = abs (Real.sqrt (x - 1) - 3) := by 
        rw [Real.sqrt_sq_eq_abs]
      exact h6
    rw [h3, h5] at h_eq
    have h4 : 2 ≤ Real.sqrt (x - 1) ∧ Real.sqrt (x - 1) ≤ 3 := by
      constructor
      · -- Prove $2 \leq \sqrt{x-1}$.
        cases' abs_cases (Real.sqrt (x - 1) - 2) with h h <;> 
          cases' abs_cases (Real.sqrt (x - 1) - 3) with k k <;> 
            try { 
              nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
            }
      · -- Prove $\sqrt{x - 1} \leq 3$.
        cases' abs_cases (Real.sqrt (x - 1) - 2) with h h <;> 
          cases' abs_cases (Real.sqrt (x - 1) - 3) with k k <;> 
            try { 
              nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
            }
    have h6 : 4 ≤ x - 1 := by
      nlinarith [Real.sqrt_nonneg (x - 1), h4.1, Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h7 : x - 1 ≤ 9 := by 
      nlinarith [Real.sqrt_nonneg (x - 1), h4.2, Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    constructor
    · -- Prove $5 \leq x$.
      linarith
    · -- Prove $x \leq 10$.
      linarith
  · -- Assume 5 ≤ x ∧ x ≤ 10, prove the equation
    rintro ⟨h5, h6⟩
    have h1 : x + 3 - 4 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h2 : x + 8 - 6 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 3) ^ 2 := by 
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h3 : Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) = abs (Real.sqrt (x - 1) - 2) := by 
      rw [h1]
      have h4 : Real.sqrt ((Real.sqrt (x - 1) - 2) ^ 2) = abs (Real.sqrt (x - 1) - 2) := by 
        rw [Real.sqrt_sq_eq_abs]
      exact h4
    have h4' : Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = abs (Real.sqrt (x - 1) - 3) := by
      rw [h2]
      have h5 : Real.sqrt ((Real.sqrt (x - 1) - 3) ^ 2) = abs (Real.sqrt (x - 1) - 3) := by 
        rw [Real.sqrt_sq_eq_abs]
      exact h5
    have h5' : 2 ≤ Real.sqrt (x - 1) := by
      have h7 : Real.sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)
      nlinarith [Real.sqrt_nonneg (x - 1), sq_nonneg (Real.sqrt (x - 1) - 2), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h6' : Real.sqrt (x - 1) ≤ 3 := by 
      have h7 : Real.sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)
      nlinarith [Real.sqrt_nonneg (x - 1), sq_nonneg (Real.sqrt (x - 1) - 3), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    rw [h3, h4']
    have eq1 : abs (Real.sqrt (x - 1) - 2) = Real.sqrt (x - 1) - 2 := by 
      rw [abs_of_nonneg]
      linarith
    have eq2 : abs (Real.sqrt (x - 1) - 3) = 3 - Real.sqrt (x - 1) := by 
      rw [abs_of_nonpos]
      · linarith
      all_goals linarith
    rw [eq1, eq2]
    linarith