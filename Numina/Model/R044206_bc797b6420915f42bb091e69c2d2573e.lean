import Mathlib

theorem algebra_169022 :
    {x : ℝ | Real.sqrt (4 * x ^ 2 + 4 * x + 1) - Real.sqrt (4 * x ^ 2 - 12 * x + 9) = 4} =
    {x : ℝ | x ≥ 3 / 2} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume h: sqrt(4x^2+4x+1) - sqrt(4x^2-12x+9) = 4, prove x ≥ 3/2
    intro h
    have h1 : Real.sqrt (4 * x ^ 2 + 4 * x + 1) = |2 * x + 1| := by
      have h2 : (4 * x ^ 2 + 4 * x + 1 : ℝ) = (2 * x + 1) ^ 2 := by ring
      rw [h2]
      rw [Real.sqrt_sq_eq_abs]
    have h2 : Real.sqrt (4 * x ^ 2 - 12 * x + 9) = |2 * x - 3| := by
      have h3 : (4 * x ^ 2 - 12 * x + 9 : ℝ) = (2 * x - 3) ^ 2 := by ring
      rw [h3]
      rw [Real.sqrt_sq_eq_abs]
    rw [h1, h2] at h
    by_cases h3 : x ≥ 3 / 2
    · -- The goal is true: x ≥ 3/2.
      tauto
    · -- Therefore, x < 3/2
      have h4 : x < (3 / 2 : ℝ) := by linarith
      by_cases h5 : x ≥ (-1 / 2 : ℝ)
      · -- -1/2 ≤ x < 3/2
        have h6 : 2 * x + 1 ≥ 0 := by linarith
        have h7 : 2 * x - 3 ≤ 0 := by linarith
        rw [abs_of_nonneg h6, abs_of_nonpos h7] at h
        nlinarith
      · -- x < -1/2
        have h8 : x < (-1 / 2 : ℝ) := by linarith
        have h6 : 2 * x + 1 < (0 : ℝ) := by linarith
        have h7 : 2 * x - 3 < (0 : ℝ) := by linarith
        rw [abs_of_neg h6, abs_of_neg h7] at h
        linarith
  · -- Assume x ≥ 3/2, prove sqrt(4x^2+4x+1) - sqrt(4x^2-12x+9) = 4
    intro h
    have h1 : Real.sqrt (4 * x ^ 2 + 4 * x + 1) = |2 * x + 1| := by
      have h2 : (4 * x ^ 2 + 4 * x + 1 : ℝ) = (2 * x + 1) ^ 2 := by ring
      rw [h2]
      rw [Real.sqrt_sq_eq_abs]
    have h2 : Real.sqrt (4 * x ^ 2 - 12 * x + 9) = |2 * x - 3| := by
      have h3 : (4 * x ^ 2 - 12 * x + 9 : ℝ) = (2 * x - 3) ^ 2 := by ring
      rw [h3]
      rw [Real.sqrt_sq_eq_abs]
    rw [h1, h2]
    have h3 : x ≥ (3 / 2 : ℝ) := by linarith
    have h4 : (2 * x + 1 : ℝ) ≥ 0 := by linarith
    have h5 : (2 * x - 3 : ℝ) ≥ 0 := by linarith
    rw [abs_of_nonneg h4, abs_of_nonneg h5]
    linarith