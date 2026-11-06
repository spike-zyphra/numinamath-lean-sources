import Mathlib

theorem algebra_186959 (x : ℝ) (h : 0 ≤ 3 * x ^ 2 + 1 ∧ 0 ≤ x ^ 2 + 3 ∧ 0 ≤ 6 * x ^ 2 + 10) :
    Real.sqrt (3 * x ^ 2 + 1) + Real.sqrt (x ^ 2 + 3) = Real.sqrt (6 * x ^ 2 + 10) ↔ x = 1 ∨ x = -1 := by

  constructor
  · -- Forward: If the equation holds, then x = ±1.
    intro heq
    have h1 : 0 ≤ 3 * x ^ 2 + 1 := h.1
    have h2 : 0 ≤ x ^ 2 + 3 := h.2.1
    have h3 : 0 ≤ 6 * x ^ 2 + 10 := h.2.2
    have heq1 : (Real.sqrt (3 * x ^ 2 + 1) + Real.sqrt (x ^ 2 + 3)) ^ 2 = (Real.sqrt (6 * x ^ 2 + 10)) ^ 2 := by
      rw [heq]
    have heq2 : (Real.sqrt (3 * x ^ 2 + 1) + Real.sqrt (x ^ 2 + 3)) ^ 2 =
        (Real.sqrt (3 * x ^ 2 + 1)) ^ 2 + (Real.sqrt (x ^ 2 + 3)) ^ 2 + 2 * (Real.sqrt (3 * x ^ 2 + 1) * Real.sqrt (x ^ 2 + 3)) := by
      ring
    have h_eq1 : (Real.sqrt (3 * x ^ 2 + 1)) ^ 2 = 3 * x ^ 2 + 1 := by
      rw [Real.sq_sqrt]
      linarith [h1]
    have h_eq2 : (Real.sqrt (x ^ 2 + 3)) ^ 2 = x ^ 2 + 3 := by
      rw [Real.sq_sqrt]
      linarith [h2]
    have h_eq3 : (Real.sqrt (6 * x ^ 2 + 10)) ^ 2 = 6 * x ^ 2 + 10 := by
      rw [Real.sq_sqrt]
      linarith [h3]
    rw [heq2] at heq1
    rw [h_eq1, h_eq2, h_eq3] at heq1
    have heq4 : Real.sqrt ((3 * x ^ 2 + 1) * (x ^ 2 + 3)) = x^2 + 3 := by
      have heq3 : Real.sqrt (3 * x ^ 2 + 1) * Real.sqrt (x ^ 2 + 3) = Real.sqrt ((3 * x ^ 2 + 1) * (x ^ 2 + 3)) := by
        rw [← Real.sqrt_mul (by nlinarith [h1, h2]) ]
      nlinarith [heq3, heq1, sq_nonneg (Real.sqrt (3 * x ^ 2 + 1) - Real.sqrt (x ^ 2 + 3)), sq_nonneg (Real.sqrt (6 * x ^ 2 + 10) - (Real.sqrt (3 * x ^ 2 + 1) + Real.sqrt (x ^ 2 + 3))), Real.sqrt_nonneg (3 * x ^ 2 + 1), Real.sqrt_nonneg (x ^ 2 + 3), Real.sqrt_nonneg (6 * x ^ 2 + 10)]
    have heq5 : (3 * x ^ 2 + 1) * (x ^ 2 + 3) = (x ^ 2 + 3) ^ 2 := by
      calc
        (3 * x ^ 2 + 1) * (x ^ 2 + 3) = (Real.sqrt ((3 * x ^ 2 + 1) * (x ^ 2 + 3))) ^ 2 := by
          rw [Real.sq_sqrt]
          nlinarith [h1, h2]
        _ = (x^2 + 3) ^ 2 := by
          rw [heq4]
        _ = (x^2 + 3) ^ 2 := by
          all_goals
            ring
    have heq6 : x^2 = 1 := by
      nlinarith 
    have heq7 : x = 1 ∨ x = -1 := by 
      have heq8 : x^2 = 1 := heq6
      have : x = 1 ∨ x = -1 := by
        rw [sq_eq_one_iff] at heq8
        assumption
      assumption
    exact heq7
  · -- Backward: If x = ±1, then the equation holds.
    rintro (h | h)
    · -- Case x = 1.
      rw [h]
      have h1 : Real.sqrt (3 * (1 : ℝ) ^ 2 + 1) = Real.sqrt 4 := by
        norm_num
      have h2 : Real.sqrt ( (1 : ℝ) ^ 2 + 3 ) = Real.sqrt 4 := by
        norm_num
      have h3 : Real.sqrt (6 * (1 : ℝ) ^ 2 + 10) = Real.sqrt 16 := by
        norm_num
      rw [h1, h2, h3]
      have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h5 : Real.sqrt (16 : ℝ) = (4 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h4] at *
      rw [h5]
      all_goals norm_num
    · -- Case x = -1.
      rw [h]
      have h1 : Real.sqrt (3 * (-1 : ℝ) ^ 2 + 1) = Real.sqrt 4 := by
        norm_num
      have h2 : Real.sqrt ((-1 : ℝ) ^ 2 + 3) = Real.sqrt 4 := by
        norm_num
      have h3 : Real.sqrt (6 * (-1 : ℝ) ^ 2 + 10) = Real.sqrt 16 := by
        norm_num
      rw [h1, h2, h3]
      have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h5 : Real.sqrt (16 : ℝ) = (4 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h4] at *
      rw [h5]
      all_goals norm_num