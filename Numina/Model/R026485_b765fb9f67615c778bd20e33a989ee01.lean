import Mathlib

theorem algebra_163977 (x y : ℝ) :
    abs (x + y + 5) + abs (x - y + 5) ≤ 10 ∧ (abs x - 5)^2 + (abs y - 12)^2 = 169 ↔
    (x = 0 ∧ y = 0) ∨ (x = -10 ∧ y = 0) := by
  constructor
  · -- Assume the conjunction, prove the disjunction
    rintro ⟨h1, h2⟩
    by_cases h11 : x + y + 5 ≥ 0
    · -- If x + y + 5 ≥ 0, consider case for x - y +5
      by_cases h12 : x - y + 5 ≥ 0
      · -- Both expressions are non-negative
        rw [abs_of_nonneg h11, abs_of_nonneg h12] at h1
        by_cases hx : x ≥ 0
        · -- x >= 0
          by_cases hy : y ≥ 0
          · -- x >=0, y >=0
            rw [abs_of_nonneg hx, abs_of_nonneg hy] at h2
            have hx0 : x = 0 := by nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ)]
            have hy0 : y = 0 := by nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ)]
            left
            exact ⟨hx0, hy0⟩
          · -- x >=0, y <0
            rw [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge (show ¬(y ≥ 0) by tauto)) ] at h2
            nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ), sq_nonneg (x - 0 : ℝ), sq_nonneg (y - 0 : ℝ)]
        · -- x <0
          by_cases hy : y ≥ 0
          · -- x <0, y >=0
            rw [abs_of_neg (lt_of_not_ge (show ¬(x ≥ 0) by tauto)), abs_of_nonneg hy] at h2
            have hx0 : x = -10 := by nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
            have hy0 : y = 0 := by nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
            right
            exact ⟨hx0, hy0⟩
          · -- x <0, y <0
            rw [abs_of_neg (lt_of_not_ge (show ¬(x ≥ 0) by tauto)), abs_of_neg (lt_of_not_ge (show ¬(y ≥ 0) by tauto)) ] at h2
            nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
      · -- Case where x + y +5 >=0, but x - y +5 <0
        rw [abs_of_nonneg h11, abs_of_neg (lt_of_not_ge (show ¬(x - y + 5 ≥ 0) by tauto)) ] at h1
        by_cases hx : x ≥ 0
        · -- x >=0
          by_cases hy : y ≥ 0
          · -- y >=0
            rw [abs_of_nonneg hx, abs_of_nonneg hy] at h2
            have hx0 : x = 0 := by nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ)]
            have hy0 : y = 0 := by nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ)]
            left
            exact ⟨hx0, hy0⟩
          · -- y <0
            rw [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge (show ¬(y ≥ 0) by tauto)) ] at h2
            nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ), sq_nonneg (x - 0 : ℝ), sq_nonneg (y - 0 : ℝ)]
        · -- x <0
          by_cases hy : y ≥ 0
          · -- y >=0
            rw [abs_of_neg (lt_of_not_ge (show ¬(x ≥ 0) by tauto)), abs_of_nonneg hy] at h2
            have hx0 : x = -10 := by nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
            have hy0 : y = 0 := by nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
            right
            exact ⟨hx0, hy0⟩
          · -- y <0
            rw [abs_of_neg (lt_of_not_ge (show ¬(x ≥ 0) by tauto)), abs_of_neg (lt_of_not_ge (show ¬(y ≥ 0) by tauto)) ] at h2
            nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
    · -- If x + y +5 <0
      by_cases h12 : x - y + 5 ≥ 0
      · -- Case where x + y +5 <0, but x - y +5 >=0
        rw [abs_of_neg (lt_of_not_ge (show ¬(x + y + 5 ≥ 0) by tauto)), abs_of_nonneg h12] at h1
        by_cases hx : x ≥ 0
        · -- x >=0
          by_cases hy : y ≥ 0
          · -- y >=0
            rw [abs_of_nonneg hx, abs_of_nonneg hy] at h2
            have hx0 : x = 0 := by nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ)]
            have hy0 : y = 0 := by nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ)]
            left
            exact ⟨hx0, hy0⟩
          · -- y <0
            rw [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge (show ¬(y ≥ 0) by tauto)) ] at h2
            nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ), sq_nonneg (x - 0 : ℝ), sq_nonneg (y - 0 : ℝ)]
        · -- x <0
          by_cases hy : y ≥ 0
          · -- y >=0
            rw [abs_of_neg (lt_of_not_ge (show ¬(x ≥ 0) by tauto)), abs_of_nonneg hy] at h2
            have hx0 : x = -10 := by nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
            have hy0 : y = 0 := by nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
            right
            exact ⟨hx0, hy0⟩
          · -- y <0
            rw [abs_of_neg (lt_of_not_ge (show ¬(x ≥ 0) by tauto)), abs_of_neg (lt_of_not_ge (show ¬(y ≥ 0) by tauto)) ] at h2
            nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
      · -- Both expressions are negative
        rw [abs_of_neg (lt_of_not_ge (show ¬(x + y + 5 ≥ 0) by tauto)), abs_of_neg (lt_of_not_ge (show ¬(x - y + 5 ≥ 0) by tauto)) ] at h1
        by_cases hx : x ≥ 0
        · -- x >=0
          by_cases hy : y ≥ 0
          · -- y >=0
            rw [abs_of_nonneg hx, abs_of_nonneg hy] at h2
            have hx0 : x = 0 := by nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ)]
            have hy0 : y = 0 := by nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ)]
            left
            exact ⟨hx0, hy0⟩
          · -- y <0
            rw [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge (show ¬(y ≥ 0) by tauto)) ] at h2
            nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ), sq_nonneg (x - 0 : ℝ), sq_nonneg (y - 0 : ℝ)]
        · -- x <0
          by_cases hy : y ≥ 0
          · -- y >=0
            rw [abs_of_neg (lt_of_not_ge (show ¬(x ≥ 0) by tauto)), abs_of_nonneg hy] at h2
            have hx0 : x = -10 := by nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
            have hy0 : y = 0 := by nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
            right
            exact ⟨hx0, hy0⟩
          · -- y <0
            rw [abs_of_neg (lt_of_not_ge (show ¬(x ≥ 0) by tauto)), abs_of_neg (lt_of_not_ge (show ¬(y ≥ 0) by tauto)) ] at h2
            nlinarith [sq_nonneg (x + 10 : ℝ), sq_nonneg (y : ℝ)]
  · -- Assume the disjunction, prove the conjunction
    rintro (h | h)
    · -- First disjunction
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num [abs]
      · norm_num [abs]
    · -- Second disjunction
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num [abs]
      · norm_num [abs]