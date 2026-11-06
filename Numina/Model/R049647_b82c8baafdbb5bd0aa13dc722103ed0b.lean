import Mathlib

theorem algebra_13637 :
    IsLeast {y : ℝ | ∃ x, y = |x + 1| + |x - 2| + |x - 3|} 4 := by
  constructor
  · -- Let's prove that 4 is in the set.
    use 2
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Let's prove that 4 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h : |x + 1| + |x - 2| + |x - 3| ≥ 4 := by
      by_cases h1 : x + 1 ≥ 0
      · -- Case 1: x + 1 ≥ 0 
        by_cases h2 : x - 2 ≥ 0
        · -- Case 1.1: x + 1 ≥ 0 and x - 2 ≥ 0
          by_cases h3 : x - 3 ≥ 0
          · -- Case 1.1.1: x + 1 ≥ 0, x - 2 ≥ 0, x - 3 ≥ 0 (x ≥ 3)
            rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3]
            linarith
          · -- Case 1.1.2: x + 1 ≥ 0, x - 2 ≥ 0, x - 3 < 0 (2 ≤ x < 3)
            rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_neg (lt_of_not_ge h3)]
            linarith
        · -- Case 1.2: x + 1 ≥ 0 and x - 2 < 0 (-1 ≤ x < 2)
          by_cases h3 : x - 3 ≥ 0
          · -- impossible: x >= -1 and x < 2, but x >= 3
            linarith
          · -- Case 1.2: x + 1 ≥ 0, x - 2 < 0, x - 3 < 0 (-1 <= x < 2)
            rw [abs_of_nonneg h1, abs_of_neg (lt_of_not_ge h2), abs_of_neg (lt_of_not_ge h3)]
            linarith
      · -- Case 2: x + 1 < 0 (x < -1)
        have h1' : x + 1 < 0 := lt_of_not_ge h1
        by_cases h2 : x - 2 ≥ 0
        · -- impossible: x < -1 and x >= 2
          linarith
        · -- Case 2.2: x + 1 < 0 and x - 2 < 0 (x < -1)
          by_cases h3 : x - 3 ≥ 0
          · -- impossible: x < -1 and x >= 3
            linarith
          · -- Case 2.2: x + 1 < 0, x - 2 < 0, x - 3 < 0 (x < -1)
            rw [abs_of_neg h1', abs_of_neg (lt_of_not_ge h2), abs_of_neg (lt_of_not_ge h3)]
            linarith
    linarith [h, hx]