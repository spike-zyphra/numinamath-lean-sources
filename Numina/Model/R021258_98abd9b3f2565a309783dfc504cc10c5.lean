import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_289143 (a : ℝ) :
  (∀ x : ℝ, abs (2 * x - a) + abs (3 * x - 2 * a) ≥ a ^ 2) ↔
  a ∈ Icc (-1 / 3) (1 / 3) := by
  constructor
  · -- Assume that for all real numbers x, |2x - a| + |3x - 2a| ≥ a², prove that a ∈ [-1/3, 1/3]
    intro h
    have h1 := h (2 * a / 3)
    have h2 : abs (2 * (2 * a / 3) - a) + abs (3 * (2 * a / 3) - 2 * a) ≥ a ^ 2 := by
      simpa using h1
    have eq1 : abs (2 * (2 * a / 3) - a) = abs (a / 3) := by
      have h3 : 2 * (2 * a / 3) - a = a / 3 := by
        linarith
      rw [h3]
    have eq2 : abs (3 * (2 * a / 3) - 2 * a) = 0 := by
      have h4 : 3 * (2 * a / 3) - 2 * a = (0 : ℝ) := by
        linarith
      rw [h4]
      norm_num
    rw [eq1, eq2] at h2
    have h3 : abs (a / 3) ≥ a ^ 2 := by
      linarith
    have h4 : -1 / 3 ≤ a := by
      cases' abs_cases (a / 3) with h5 h5 <;> nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (a + 1 / 3)]
    have h5 : a ≤ 1 / 3 := by
      cases' abs_cases (a / 3) with h5 h5 <;> nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (a + 1 / 3)]
    exact ⟨by linarith, by linarith⟩
  · -- Assume a ∈ [-1/3, 1/3], prove ∀ x, |2x - a| + |3x - 2a| ≥ a²
    rintro (⟨h1, h2⟩)
    intro x
    have h3 : -1 / 3 ≤ a := by linarith [h1]
    have h4 : a ≤ 1 / 3 := by linarith [h2]
    by_cases h5 : 2 * x - a ≥ 0
    · -- Case where 2x - a ≥ 0
      rw [abs_of_nonneg h5]
      by_cases h6 : 3 * x - 2 * a ≥ 0
      · -- Case where both expressions are non-negative
        rw [abs_of_nonneg h6]
        nlinarith [sq_nonneg (x - 2 * a / 3), sq_nonneg (a), sq_nonneg (x - a / 2), sq_nonneg (a - 1 / 3), sq_nonneg (a + 1 / 3)]
      · -- Case where 3x - 2a < 0
        rw [abs_of_neg (not_le.mp h6)]
        nlinarith [sq_nonneg (x - 2 * a / 3), sq_nonneg (a), sq_nonneg (x - a / 2), sq_nonneg (a - 1 / 3), sq_nonneg (a + 1 / 3)]
    · -- Case where 2x - a < 0
      rw [abs_of_neg (not_le.mp h5)]
      by_cases h6 : 3 * x - 2 * a ≥ 0
      · -- Case where 3x - 2a ≥ 0
        rw [abs_of_nonneg h6]
        nlinarith [sq_nonneg (x - 2 * a / 3), sq_nonneg (a), sq_nonneg (x - a / 2), sq_nonneg (a - 1 / 3), sq_nonneg (a + 1 / 3)]
      · -- Case where 3x - 2a < 0
        rw [abs_of_neg (not_le.mp h6)]
        nlinarith [sq_nonneg (x - 2 * a / 3), sq_nonneg (a), sq_nonneg (x - a / 2), sq_nonneg (a - 1 / 3), sq_nonneg (a + 1 / 3)]