import Mathlib

theorem algebra_129800 (x y : ℤ) :
    |x^2 + 2 * x * y - 3 * y^2| = 1 ↔ (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) := by
  constructor
  · -- Forward direction: equation holds implies points
    intro h
    have h1 : x^2 + 2 * x * y - 3 * y^2 = 1 ∨ x^2 + 2 * x * y - 3 * y^2 = -1 := by
      cases' abs_cases (x^2 + 2 * x * y - 3 * y^2) with h2 h2
      · -- Case where |A| = 1, A ≥ 0, so A = 1
        left
        linarith
      · -- Case where |A| = 1, A < 0, so A = -1
        right
        linarith
    rcases h1 with (h1 | h1)
    · -- Case 1: expression = 1
      have h2 : (x - y) * (x + 3 * y) = 1 := by
        nlinarith 
      have h3 : x - y = 1 ∨ x - y = -1 := by 
        apply Int.eq_one_or_neg_one_of_mul_eq_one
        exact h2
      rcases h3 with (h3 | h3)
      · -- Case 1a: x - y = 1
        have h4 : x + 3 * y = 1 := by
          nlinarith 
        have hy : y = 0 := by 
          omega 
        have hx : x = 1 := by 
          omega 
        left 
        simp [hx, hy]
      · -- Case 1b: x - y = -1
        have h4 : x + 3 * y = -1 := by
          nlinarith
        have hy : y = 0 := by 
          omega 
        have hx : x = -1 := by 
          omega 
        right 
        simp [hx, hy]
    · -- Case 2: expression = -1
      have h2 : (x - y) * (x + 3 * y) = -1 := by 
        nlinarith 
      have h3 : x - y = 1 ∨ x - y = -1 := by 
        apply Int.eq_one_or_neg_one_of_mul_eq_neg_one 
        exact h2
      rcases h3 with (h3 | h3)
      · -- Case 2a: x - y = 1
        have h4 : x + 3 * y = -1 := by
          nlinarith [h3, h2]
        exfalso 
        omega 
      · -- Case 2b: x - y = -1
        have h4 : x + 3 * y = 1 := by 
          nlinarith [h3, h2]
        exfalso 
        omega
  · -- Backward direction: points imply equation
    rintro (h | h)
    · -- Case where (x = 1 ∧ y = 0)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num [abs_of_nonneg]
    · -- Case where (x = -1 ∧ y = 0)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num [abs_of_nonneg]