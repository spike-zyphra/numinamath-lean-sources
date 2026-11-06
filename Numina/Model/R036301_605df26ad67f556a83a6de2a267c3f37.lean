import Mathlib

/- Given that the rational number $x$ satisfies $-5 \leq x \leq 3$, the maximum value of the expression $\left|  x+3\right|  +\left|  x-2\right|$ is ___          ___ , and the minimum value is ___          ___. -/
theorem algebra_7948 :
    IsGreatest {y : ℚ | ∃ x, -5 ≤ x ∧ x ≤ 3 ∧ y = abs (x + 3) + abs (x - 2)} 9 ∧
    IsLeast {y : ℚ | ∃ x, -5 ≤ x ∧ x ≤ 3 ∧ y = abs (x + 3) + abs (x - 2)} 5 := by
  constructor 
  · -- We need to show that 9 is in the set and it is the greatest
    constructor 
    · -- Show that 9 is in the set
      use -5 
      norm_num [abs]
    · -- Show that for any y in the set, y ≤ 9
      intro y hy 
      rcases hy with ⟨x, hx1, hx2, heq⟩ 
      have h1 : abs (x + 3 : ℚ) + abs (x - 2 : ℚ) ≤ 9 := by
        by_cases h1 : x + 3 ≥ 0 
        · -- Case where x + 3 ≥ 0, i.e., x ≥ -3
          by_cases h2 : x - 2 ≥ 0 
          · -- Case where x - 2 ≥ 0, i.e., x ≥ 2
            rw [abs_of_nonneg h1, abs_of_nonneg h2]
            linarith 
          · -- Case where x - 2 < 0, i.e., x < 2
            rw [abs_of_nonneg h1, abs_of_neg (lt_of_not_ge h2)]
            linarith 
        · -- Case where x + 3 < 0, i.e., x < -3
          by_cases h2 : x - 2 ≥ 0 
          · -- Case where x - 2 ≥ 0, i.e., x ≥ 2
            rw [abs_of_neg (lt_of_not_ge h1), abs_of_nonneg h2]
            linarith 
          · -- Case where x - 2 < 0, i.e., x < 2
            rw [abs_of_neg (lt_of_not_ge h1), abs_of_neg (lt_of_not_ge h2)]
            linarith 
      linarith [heq, h1]
  · -- We need to show that 5 is in the set and it is the least
    constructor 
    · -- Show that 5 is in the set
      use (0 : ℚ)
      norm_num [abs]
    · -- Show that for any y in the set, 5 ≤ y
      intro y hy 
      rcases hy with ⟨x, hx1, hx2, heq⟩ 
      have h2 : abs (x + 3 : ℚ) + abs (x - 2 : ℚ) ≥ 5 := by
        by_cases h1 : x + 3 ≥ 0 
        · -- Case where x + 3 ≥ 0, i.e., x ≥ -3
          by_cases h2 : x - 2 ≥ 0 
          · --  Case where x - 2 ≥ 0, i.e., x ≥ 2
            rw [abs_of_nonneg h1, abs_of_nonneg h2]
            linarith 
          · -- Case where x - 2 < 0, i.e., x < 2
            rw [abs_of_nonneg h1, abs_of_neg (lt_of_not_ge h2)]
            linarith 
        · -- Case where x + 3 < 0, i.e., x < -3
          by_cases h2 : x - 2 ≥ 0 
          · -- Case where x - 2 ≥ 0, i.e., x ≥ 2
            rw [abs_of_neg (lt_of_not_ge h1), abs_of_nonneg h2]
            linarith 
          · -- Case where x - 2 < 0, i.e., x < 2
            rw [abs_of_neg (lt_of_not_ge h1), abs_of_neg (lt_of_not_ge h2)]
            linarith 
      linarith [heq, h2]