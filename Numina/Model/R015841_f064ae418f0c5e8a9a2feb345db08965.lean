import Mathlib

theorem algebra_104811 (x y : ℝ) :
    abs x + abs y = 1340 ∧ x^3 + y^3 + 2010 * x * y = 670^3 ↔
    (x = -670 ∧ y = -670) ∨ (x = 1005 ∧ y = -335) ∨ (x = -335 ∧ y = 1005) := by
  constructor
  · -- Assume the conditions hold, prove the disjunction of the solutions.
    rintro ⟨h1, h2⟩
    by_cases h3 : x ≥ 0
    · -- Case where x ≥ 0.
      by_cases h4 : y ≥ 0
      · -- Case where x ≥ 0 and y ≥ 0.
        rw [abs_of_nonneg h3, abs_of_nonneg h4] at h1
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 670), sq_nonneg (y - 670), sq_nonneg (x + y - 670)]
      · -- Case where x ≥ 0 and y < 0.
        rw [abs_of_nonneg h3, abs_of_neg (not_le.mp h4)] at h1
        have h5 : x + y = 670 := by
          nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 670), sq_nonneg (x - 1005), sq_nonneg (y + 335)]
        have hx1 : x = 1005 := by
          nlinarith [sq_nonneg (x - 1005), sq_nonneg (y + 335)]
        have hy1 : y = -335 := by
          linarith [h5, hx1]
        right
        left
        exact ⟨hx1, hy1⟩
    · -- Case where x < 0.
      by_cases h4 : y ≥ 0
      · -- Case where x < 0 and y ≥ 0.
        rw [abs_of_neg (not_le.mp h3), abs_of_nonneg h4] at h1
        have h5 : x + y = 670 := by
          nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 670), sq_nonneg (x + 335), sq_nonneg (y - 1005)]
        have hx1 : x = -335 := by
          nlinarith [sq_nonneg (x + 335), sq_nonneg (y - 1005)]
        have hy1 : y = 1005 := by
          linarith [h5, hx1]
        right
        right
        exact ⟨hx1, hy1⟩
      · -- Case where x < 0 and y < 0.
        rw [abs_of_neg (not_le.mp h3), abs_of_neg (not_le.mp h4)] at h1
        have hx2 : x = -670 := by
          nlinarith [sq_nonneg (x + y + 1340), sq_nonneg (x + 670), sq_nonneg (y + 670)]
        have hy2 : y = -670 := by
          nlinarith [sq_nonneg (x + y + 1340), sq_nonneg (x + 670), sq_nonneg (y + 670)]
        left
        exact ⟨hx2, hy2⟩
  · -- Assume one of the solutions, prove the conditions.
    rintro (h | h | h)
    · -- Case (-670, -670).
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- Check abs (-670 : ℝ) + abs (-670 : ℝ) = 1340.
        norm_num [abs_of_nonpos]
      · -- Check (-670 : ℝ)^3 + (-670 : ℝ)^3 + 2010 * (-670) * (-670) = 670^3.
        norm_num
    · -- Case (1005, -335).
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- Check abs (1005 : ℝ) + abs (-335 : ℝ) = 1340.
        norm_num [abs_of_pos, abs_of_neg]
      · -- Check (1005 : ℝ)^3 + (-335 : ℝ)^3 + 2010 * 1005 * (-335) = 670^3.
        norm_num
    · -- Case (-335, 1005).
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- Check abs (-335 : ℝ) + abs (1005 : ℝ) = 1340.
        norm_num [abs_of_neg, abs_of_pos]
      · -- Check (-335 : ℝ)^3 + (1005 : ℝ)^3 + 2010 * (-335) * 1005 = 670^3.
        norm_num