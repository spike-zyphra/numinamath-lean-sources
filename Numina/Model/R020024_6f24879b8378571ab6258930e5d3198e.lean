import Mathlib

theorem algebra_191756 (x : ℝ) (hx : 0 ≤ 2 * x + 1) :
    Real.sqrt (2 * x + 2 - 2 * Real.sqrt (2 * x + 1)) +
    Real.sqrt (2 * x + 10 - 6 * Real.sqrt (2 * x + 1)) = 2 ↔
    x ∈ Set.Icc 0 4 := by
  constructor
  · -- Assume the equation holds, prove x ∈ [0, 4]
    intro h_eq
    have h1 : Real.sqrt (2 * x + 2 - 2 * Real.sqrt (2 * x + 1)) = abs (Real.sqrt (2 * x + 1) - 1) := by
      have h2 : (2 * x + 2 - 2 * Real.sqrt (2 * x + 1) ) = (Real.sqrt (2 * x + 1) - 1) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show 0 ≤ (2 * x + 1 : ℝ) by linarith)]
      rw [h2]
      have h3 : Real.sqrt ((Real.sqrt (2 * x + 1) - 1) ^ 2) = abs (Real.sqrt (2 * x + 1) - 1) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h3
    have h4 : Real.sqrt (2 * x + 10 - 6 * Real.sqrt (2 * x + 1)) = abs (Real.sqrt (2 * x + 1) - 3) := by
      have h5 : (2 * x + 10 - 6 * Real.sqrt (2 * x + 1) ) = (Real.sqrt (2 * x + 1) - 3) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show 0 ≤ (2 * x + 1 : ℝ) by linarith)]
      rw [h5]
      have h6 : Real.sqrt ((Real.sqrt (2 * x + 1) - 3) ^ 2) = abs (Real.sqrt (2 * x + 1) - 3) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h6
    rw [h1, h4] at h_eq
    have h7 : 1 ≤ Real.sqrt (2 * x + 1) ∧ Real.sqrt (2 * x + 1) ≤ 3 := by
      constructor
      · -- Prove 1 ≤ Real.sqrt (2 * x + 1)
        cases' abs_cases (Real.sqrt (2 * x + 1) - 1) with h11 h11 <;> 
        cases' abs_cases (Real.sqrt (2 * x + 1) - 3) with h12 h12 <;> 
        try { 
          nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show 0 ≤ (2 * x + 1 : ℝ) by linarith)]
        }
      · -- Prove Real.sqrt (2 * x + 1) ≤ 3
        cases' abs_cases (Real.sqrt (2 * x + 1) - 1) with h11 h11 <;> 
        cases' abs_cases (Real.sqrt (2 * x + 1) - 3) with h12 h12 <;> 
        try { 
          nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show 0 ≤ (2 * x + 1 : ℝ) by linarith)]
        }
    have h8 : 0 ≤ x := by
      nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show 0 ≤ (2 * x + 1 : ℝ) by linarith), h7.1]
    have h9 : x ≤ 4 := by
      nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show 0 ≤ (2 * x + 1 : ℝ) by linarith), h7.2]
    exact ⟨h8, h9⟩
  · -- Assume x ∈ [0, 4], prove the equation
    rintro ⟨hx0, hx4⟩
    have h1 : Real.sqrt (2 * x + 2 - 2 * Real.sqrt (2 * x + 1)) = abs (Real.sqrt (2 * x + 1) - 1) := by
      have h2 : (2 * x + 2 - 2 * Real.sqrt (2 * x + 1) ) = (Real.sqrt (2 * x + 1) - 1) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show 0 ≤ (2 * x + 1 : ℝ) by linarith)]
      rw [h2]
      have h3 : Real.sqrt ((Real.sqrt (2 * x + 1) - 1) ^ 2) = abs (Real.sqrt (2 * x + 1) - 1) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h3
    have h4 : Real.sqrt (2 * x + 10 - 6 * Real.sqrt (2 * x + 1)) = abs (Real.sqrt (2 * x + 1) - 3) := by
      have h5 : (2 * x + 10 - 6 * Real.sqrt (2 * x + 1) ) = (Real.sqrt (2 * x + 1) - 3) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show 0 ≤ (2 * x + 1 : ℝ) by linarith)]
      rw [h5]
      have h6 : Real.sqrt ((Real.sqrt (2 * x + 1) - 3) ^ 2) = abs (Real.sqrt (2 * x + 1) - 3) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h6
    rw [h1, h4]
    have h7 : 1 ≤ Real.sqrt (2 * x + 1) := by
      nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show 0 ≤ (2 * x + 1 : ℝ) by linarith)]
    have h8 : Real.sqrt (2 * x + 1) ≤ 3 := by
      nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show 0 ≤ (2 * x + 1 : ℝ) by linarith)]
    have h9 : abs (Real.sqrt (2 * x + 1) - 1) = Real.sqrt (2 * x + 1) - 1 := by
      rw [abs_of_nonneg]
      nlinarith [Real.sqrt_nonneg (2 * x + 1)]
    have h10 : abs (Real.sqrt (2 * x + 1) - 3) = 3 - Real.sqrt (2 * x + 1) := by
      rw [abs_of_nonpos]
      linarith [Real.sqrt_nonneg (2 * x + 1)]
      all_goals linarith [Real.sqrt_nonneg (2 * x + 1)]
    rw [h9, h10]
    all_goals nlinarith [Real.sqrt_nonneg (2 * x + 1)]