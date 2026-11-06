import Mathlib

open Real Set

theorem algebra_300702 :
    IsLeast {M : ℝ | ∃ x y : ℝ, M = max (max (x^2 + 2 * x * y + y^2) (x^2 - 2 * x * y + y^2)) (x^2 + 4 * x + 4)} 1 := by
  constructor
  · -- Show that 1 can be obtained, so 1 is in the set
    use -1, 0
    norm_num [max_eq_left, max_eq_right]
  · -- Now prove that for any M in the set, 1 ≤ M
    intro M h
    rcases h with ⟨x, y, h_eq⟩
    by_cases h1 : x^2 + 2 * x * y + y^2 ≥ x^2 - 2 * x * y + y^2
    · -- In this case, max (x^2 + 2 * x * y + y^2) (x^2 - 2 * x * y + y^2) = x^2 + 2 * x * y + y^2
      have h2 : max (x^2 + 2 * x * y + y^2) (x^2 - 2 * x * y + y^2) = x^2 + 2 * x * y + y^2 := by
        apply max_eq_left h1
      rw [h2] at h_eq
      by_cases h2 : x^2 + 2 * x * y + y^2 ≥ x^2 + 4 * x + 4
      · -- In this case, max (x^2 + 2 * x * y + y^2) (x^2 + 4 * x + 4) = x^2 + 2 * x * y + y^2
        have h3 : max (x^2 + 2 * x * y + y^2) (x^2 + 4 * x + 4) = x^2 + 2 * x * y + y^2 := by
          apply max_eq_left h2
        rw [h3] at h_eq
        nlinarith [sq_nonneg (x - (-1)), sq_nonneg (y - 0), sq_nonneg (x - y), sq_nonneg (x + y + 2)]
      · -- In this case, max (x^2 + 2 * x * y + y^2) (x^2 + 4 * x + 4) = x^2 + 4 * x + 4
        have h3 : max (x^2 + 2 * x * y + y^2) (x^2 + 4 * x + 4) = x^2 + 4 * x + 4 := by
          apply max_eq_right (le_of_not_ge h2)
        rw [h3] at h_eq
        nlinarith [sq_nonneg (x - (-1)), sq_nonneg (y - 0), sq_nonneg (x - y), sq_nonneg (x + y + 2)]
    · -- In this case, max (x^2 + 2 * x * y + y^2) (x^2 - 2 * x * y + y^2) = x^2 - 2 * x * y + y^2
      have h2 : max (x^2 + 2 * x * y + y^2) (x^2 - 2 * x * y + y^2) = x^2 - 2 * x * y + y^2 := by
        apply max_eq_right (le_of_not_ge h1)
      rw [h2] at h_eq
      by_cases h2 : x^2 - 2 * x * y + y^2 ≥ x^2 + 4 * x + 4
      · -- In this case, max (x^2 - 2 * x * y + y^2) (x^2 + 4 * x + 4) = x^2 - 2 * x * y + y^2
        have h3 : max (x^2 - 2 * x * y + y^2) (x^2 + 4 * x + 4) = x^2 - 2 * x * y + y^2 := by
          apply max_eq_left h2
        rw [h3] at h_eq
        nlinarith [sq_nonneg (x - (-1)), sq_nonneg (y - 0), sq_nonneg (x - y), sq_nonneg (x + y + 2)]
      · -- In this case, max (x^2 - 2 * x * y + y^2) (x^2 + 4 * x + 4) = x^2 + 4 * x + 4
        have h3 : max (x^2 - 2 * x * y + y^2) (x^2 + 4 * x + 4) = x^2 + 4 * x + 4 := by
          apply max_eq_right (le_of_not_ge h2)
        rw [h3] at h_eq
        nlinarith [sq_nonneg (x - (-1)), sq_nonneg (y - 0), sq_nonneg (x - y), sq_nonneg (x + y + 2)]