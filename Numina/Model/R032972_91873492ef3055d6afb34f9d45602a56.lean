import Mathlib

theorem algebra_260219 (x : ℝ) :
    3 * Real.sqrt ((x + 1)^2) + Real.sqrt (x^2 - 4 * x + 4) =
    abs (1 + 6 * x) - 4 * abs (x - 1) ↔ x ∈ Set.Icc 1 2 := by
  constructor
  · -- Forward: if the equation holds, then x ∈ [1, 2]
    intro h
    have h1 : Real.sqrt ((x + 1) ^ 2) = |x + 1| := by 
      rw [Real.sqrt_sq_eq_abs]
    have h2 : Real.sqrt (x^2 - 4 * x + 4) = |x - 2| := by
      have h3 : x ^ 2 - 4 * x + 4 = (x - 2) ^ 2 := by
        ring
      rw [h3]
      rw [Real.sqrt_sq_eq_abs]
    rw [h1, h2] at h
    by_cases h3 : x ≥ 2
    · -- Case 1: x ≥ 2
      rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith)] at h
      rw [abs_of_nonneg (show (1 + 6 * x) ≥ 0 by linarith), abs_of_nonneg (show (x - 1) ≥ 0 by linarith)] at h
      have h4 : x = 2 := by
        nlinarith
      rw [show x = 2 by linarith]
      norm_num [Set.mem_Icc]
    · -- Case 2: x < 2
      by_cases h4 : x ≥ 1
      · -- Case 2a: 1 ≤ x < 2
        rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith)] at h
        rw [abs_of_nonneg (show (1 + 6 * x) ≥ 0 by linarith), abs_of_nonneg (show (x - 1) ≥ 0 by linarith)] at h
        constructor <;> linarith
      · -- Case 3: x < 1
        by_cases h5 : x ≥ -1 / 6
        · -- Case 3a: -1/6 ≤ x < 1
          rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith)] at h
          rw [abs_of_nonneg (show (1 + 6 * x) ≥ 0 by linarith), abs_of_nonpos (show (x - 1) ≤ 0 by linarith)] at h
          have h6 : x = 1 := by
            linarith
          have h7 : x < (1 : ℝ) := by linarith
          linarith
        · -- Case 4: x < -1/6
          by_cases h8 : x ≥ -1
          · -- Subcase 4a: -1 ≤ x < -1/6
            rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith)] at h
            rw [abs_of_nonpos (show (1 + 6 * x) ≤ 0 by linarith), abs_of_nonpos (show (x - 1) ≤ 0 by linarith)] at h
            nlinarith
          · -- Case 4b: x < -1
            rw [abs_of_nonpos (show x + 1 ≤ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith)] at h
            rw [abs_of_nonpos (show (1 + 6 * x) ≤ 0 by linarith), abs_of_nonpos (show (x - 1) ≤ 0 by linarith)] at h
            nlinarith
  · -- Backward: if x ∈ [1, 2], then the equation holds
    rintro ⟨hx1, hx2⟩
    have h1 : Real.sqrt ((x + 1) ^ 2) = |x + 1| := by 
      rw [Real.sqrt_sq_eq_abs]
    have h2 : Real.sqrt (x^2 - 4 * x + 4) = |x - 2| := by
      have h3 : x ^ 2 - 4 * x + 4 = (x - 2) ^ 2 := by
        ring
      rw [h3]
      rw [Real.sqrt_sq_eq_abs]
    rw [h1, h2]
    have h3 : x - 2 ≤ 0 := by linarith
    have h4 : x + 1 ≥ 0 := by linarith
    have h5 : 1 + 6 * x ≥ 0 := by linarith
    have h6 : x - 1 ≥ 0 := by linarith
    rw [abs_of_nonneg h4, abs_of_nonpos h3]
    rw [abs_of_nonneg h5, abs_of_nonneg h6]
    all_goals nlinarith