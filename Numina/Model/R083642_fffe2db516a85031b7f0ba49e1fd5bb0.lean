import Mathlib

open Real Set

theorem inequalities_227568 (x y : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) :
    min (min (min (x^2 + x * y + y^2) (x^2 + x * (y - 1) + (y - 1)^2)) ((x - 1)^2 + (x - 1) * y + y^2)) ((x - 1)^2 + (x - 1) * (y - 1) + (y - 1)^2) ≤ 1 / 3 := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  by_cases h1 : x^2 + x * y + y^2 ≤ x^2 + x * (y - 1) + (y - 1)^2
  · -- In this case, the first expression is the smallest among the first two
    rw [min_eq_left h1]
    by_cases h2 : x^2 + x * y + y^2 ≤ (x - 1)^2 + (x - 1) * y + y^2
    · -- The first expression is the smallest among the first three
      rw [min_eq_left h2]
      by_cases h3 : x^2 + x * y + y^2 ≤ (x - 1)^2 + (x - 1) * (y - 1) + (y - 1)^2
      · -- The first expression is the smallest
        rw [min_eq_left h3]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2)]
      · -- The last expression is smaller
        rw [min_eq_right (le_of_not_le h3)]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2)]
    · -- The third expression is smaller among the first three
      rw [min_eq_right (le_of_not_le h2)]
      by_cases h4 : (x - 1)^2 + (x - 1) * y + y^2 ≤ (x - 1)^2 + (x - 1) * (y - 1) + (y - 1)^2
      · -- The third expression is the smallest
        rw [min_eq_left h4]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2)]
      · -- The last expression is smaller
        rw [min_eq_right (le_of_not_le h4)]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2)]
  · -- The second expression is smaller among the first two
    rw [min_eq_right (le_of_not_le h1)]
    by_cases h4 : x^2 + x * (y - 1) + (y - 1)^2 ≤ (x - 1)^2 + (x - 1) * y + y^2
    · -- The second expression is the smallest among the first three
      rw [min_eq_left h4]
      by_cases h5 : x^2 + x * (y - 1) + (y - 1)^2 ≤ (x - 1)^2 + (x - 1) * (y - 1) + (y - 1)^2
      · -- The second expression is the smallest
        rw [min_eq_left h5]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2)]
      · -- The last expression is smaller
        rw [min_eq_right (le_of_not_le h5)]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2)]
    · -- The third expression is smaller among the first three
      rw [min_eq_right (le_of_not_le h4)]
      by_cases h6 : (x - 1)^2 + (x - 1) * y + y^2 ≤ (x - 1)^2 + (x - 1) * (y - 1) + (y - 1)^2
      · -- The third expression is the smallest
        rw [min_eq_left h6]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2)]
      · -- The last expression is smaller
        rw [min_eq_right (le_of_not_le h6)]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2)]