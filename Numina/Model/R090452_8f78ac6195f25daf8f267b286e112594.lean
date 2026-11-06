import Mathlib

theorem algebra_251763 (x : ℝ) : (1 - 2 * x) / (3 - abs (x - 1)) = 1 ↔ x = -1 / 3 := by
  constructor
  · -- Forward direction: If equation holds, prove x = -1/3
    intro h_eq
    have h1 : 3 - abs (x - 1) ≠ 0 := by
      by_contra h_zero
      have : (1 - 2 * x) / (3 - abs (x - 1)) = 0 := by
        rw [h_zero]
        norm_num
      linarith [h_eq, this]
    have eq1 : 1 - 2 * x = 3 - abs (x - 1) := by
      field_simp [h1] at h_eq
      linarith
    by_cases h2 : x - 1 ≥ 0
    · -- Case 1: x - 1 ≥ 0, i.e., x ≥ 1
      rw [abs_of_nonneg h2] at eq1
      have h3 : x = -3 := by linarith
      linarith
    · -- Case 2: x - 1 < 0, i.e., x < 1
      have h3 : x - 1 < 0 := by linarith
      rw [abs_of_neg h3] at eq1
      have hx : x = -1 / 3 := by linarith
      exact hx
  · -- Backward direction: If x = -1/3, prove equation holds
    intro h_eq
    rw [h_eq]
    norm_num [abs_of_neg]
    <;> norm_num