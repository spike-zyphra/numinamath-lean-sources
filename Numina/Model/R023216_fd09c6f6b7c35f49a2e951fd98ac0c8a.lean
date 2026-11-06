import Mathlib

theorem algebra_186800 (x : ℝ) (hx : x ≥ 0) :
    Real.sqrt (x + Real.sqrt (x + 11)) + Real.sqrt (x - Real.sqrt (x + 11)) = 4 ↔ x = 5 := by
  constructor
  · -- Forward direction: assume the equation, prove x=5
    intro h
    by_cases h1 : x - Real.sqrt (x + 11) ≥ 0
    · -- If x - Real.sqrt (x + 11) ≥ 0, then the domain is valid.
      have h2 : Real.sqrt (x - Real.sqrt (x + 11)) ≥ 0 := by positivity
      have h3 : (Real.sqrt (x + Real.sqrt (x + 11)) + Real.sqrt (x - Real.sqrt (x + 11))) ^ 2 = 16 := by nlinarith [h, Real.sqrt_nonneg (x + Real.sqrt (x + 11)), Real.sqrt_nonneg (x - Real.sqrt (x + 11))]
      have h4 : (Real.sqrt (x + Real.sqrt (x + 11))) ^ 2 = x + Real.sqrt (x + 11) := by
        rw [Real.sq_sqrt]
        nlinarith [Real.sqrt_nonneg (x + 11), Real.sq_sqrt (show 0 ≤ x + 11 by linarith)]
      have h5 : (Real.sqrt (x - Real.sqrt (x + 11))) ^ 2 = x - Real.sqrt (x + 11) := by
        rw [Real.sq_sqrt]
        nlinarith
      -- Expanding the squared expression
      have h6 : (Real.sqrt (x + Real.sqrt (x + 11)) + Real.sqrt (x - Real.sqrt (x + 11))) ^ 2 =
          (Real.sqrt (x + Real.sqrt (x + 11))) ^ 2 + (Real.sqrt (x - Real.sqrt (x + 11))) ^ 2 + 2 * (Real.sqrt (x + Real.sqrt (x + 11)) * Real.sqrt (x - Real.sqrt (x + 11))) := by ring
      rw [h6] at h3
      rw [h4, h5] at h3
      -- Multiplication of the two square expressions
      have h7 : Real.sqrt (x + Real.sqrt (x + 11)) * Real.sqrt (x - Real.sqrt (x + 11)) = Real.sqrt (x ^ 2 - x - 11) := by
        have h8 : (x + Real.sqrt (x + 11)) * (x - Real.sqrt (x + 11)) = x ^ 2 - x - 11 := by 
          nlinarith [Real.sqrt_nonneg (x + 11), Real.sq_sqrt (show 0 ≤ x + 11 by linarith)]
        have h9 : Real.sqrt (x + Real.sqrt (x + 11)) * Real.sqrt (x - Real.sqrt (x + 11)) = Real.sqrt ((x + Real.sqrt (x + 11)) * (x - Real.sqrt (x + 11))) := by
          rw [Real.sqrt_mul (by
            nlinarith [Real.sqrt_nonneg (x + 11), Real.sq_sqrt (show 0 ≤ x + 11 by linarith)]
          )
          ]
        rw [h9, h8]
      have h8 : x ^ 2 - x - 11 = (8 - x) ^ 2 := by
        have h9 : Real.sqrt (x ^ 2 - x - 11) = 8 - x := by
          nlinarith [Real.sqrt_nonneg (x ^ 2 - x - 11), Real.sq_sqrt (show 0 ≤ x ^ 2 - x - 11 by nlinarith [Real.sqrt_nonneg (x + 11), Real.sq_sqrt (show 0 ≤ x + 11 by linarith)]), h1]
        have h11 : (Real.sqrt (x ^ 2 - x - 11)) ^ 2 = (8 - x) ^ 2 := by
          rw [h9]
        have h12 : (Real.sqrt (x ^ 2 - x - 11)) ^ 2 = x ^ 2 - x - 11 := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg (x + 11), Real.sq_sqrt (show 0 ≤ x + 11 by linarith)]
        nlinarith [h11, h12]
      -- Solving the quadratic
      have h10 : x = 5 := by
        nlinarith [sq_nonneg (x - 5), h1]
      exact h10
    · -- Case where the domain is not valid, so the expression becomes Real.sqrt (x + sqrt (x + 11)) = 4
      have h2 : Real.sqrt (x - Real.sqrt (x + 11)) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
        all_goals linarith
      have h3 : Real.sqrt (x + Real.sqrt (x + 11)) = 4 := by linarith [h, h2]
      have h4 : Real.sqrt (x + Real.sqrt (x + 11)) ≥ 0 := by positivity
      have h5 : (Real.sqrt (x + Real.sqrt (x + 11))) ^ 2 = 16 := by
        nlinarith [Real.sqrt_nonneg (x + Real.sqrt (x + 11)), h3]
      have h6 : (Real.sqrt (x + Real.sqrt (x + 11))) ^ 2 = x + Real.sqrt (x + 11) := by
        rw [Real.sq_sqrt]
        nlinarith [Real.sqrt_nonneg (x + 11), Real.sq_sqrt (show 0 ≤ x + 11 by linarith)]
      have h7 : x + Real.sqrt (x + 11) = 16 := by linarith [h5, h6]
      have h8 : x + 11 = (16 - x) ^ 2 := by
        have h9 : Real.sqrt (x + 11) = 16 - x := by
          nlinarith [Real.sqrt_nonneg (x + 11), Real.sq_sqrt (show 0 ≤ x + 11 by linarith), h7]
        nlinarith [Real.sqrt_nonneg (x + 11), Real.sq_sqrt (show 0 ≤ x + 11 by linarith), h9]
      -- Solving the quadratic
      have h9 : x = 5 := by
        nlinarith [sq_nonneg (x - 5), sq_nonneg (x - 5)]
      exact h9
  · -- Backward: if x=5, prove the equation
    intro h
    rw [h]
    have h1 : Real.sqrt (5 + Real.sqrt (5 + 11)) = 3 := by
      have h2 : Real.sqrt (5 + 11) = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h2]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt (5 - Real.sqrt (5 + 11)) = 1 := by
      have h2 : Real.sqrt (5 + 11) = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h2]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h3]
    all_goals norm_num