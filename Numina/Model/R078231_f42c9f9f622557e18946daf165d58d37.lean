import Mathlib

/- If $x$ is any real number, then the minimum value of $\left| x+1 \right|+\left| x+2 \right|+\left| x+3 \right|+\left| x+4 \right|+\left| x+5 \right|$ is ___          ___. -/
theorem algebra_2504 :
  IsLeast {y : ℝ | ∃ x, y = abs (x + 1) + abs (x + 2) + abs (x + 3) + abs (x + 4) + abs (x + 5)} 6 := by
  constructor
  · -- First, we prove that 6 is in the set, achieved when x = -3
    use -3
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Now, we need to prove that 6 is the smallest value
    intro y hy
    rcases hy with ⟨x, hx⟩
    by_cases h1 : x + 1 >= 0
    · -- Case where x + 1 >= 0
      rw [abs_of_nonneg h1] at hx
      by_cases h2 : x + 2 >= 0
      · -- Case where x + 2 >= 0
        rw [abs_of_nonneg h2] at hx
        by_cases h3 : x + 3 >= 0
        · -- Case where x + 3 >= 0
          rw [abs_of_nonneg h3] at hx
          by_cases h4 : x + 4 >= 0
          · -- Case where x + 4 >= 0
            rw [abs_of_nonneg h4] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
          · -- Case where x + 4 < 0
            rw [abs_of_neg (not_le.mp h4)] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
        · -- Case where x + 3 < 0
          rw [abs_of_neg (not_le.mp h3)] at hx
          by_cases h4 : x + 4 >= 0
          · -- Case where x + 4 >= 0
            rw [abs_of_nonneg h4] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
          · -- Case where x + 4 < 0
            rw [abs_of_neg (not_le.mp h4)] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
      · -- Case where x + 2 < 0
        rw [abs_of_neg (not_le.mp h2)] at hx
        by_cases h3 : x + 3 >= 0
        · -- Case where x + 3 >= 0
          rw [abs_of_nonneg h3] at hx
          by_cases h4 : x + 4 >= 0
          · -- Case where x + 4 >= 0
            rw [abs_of_nonneg h4] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
          · -- Case where x + 4 < 0
            rw [abs_of_neg (not_le.mp h4)] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
        · -- Case where x + 3 < 0
          rw [abs_of_neg (not_le.mp h3)] at hx
          by_cases h4 : x + 4 >= 0
          · -- Case where x + 4 >= 0
            rw [abs_of_nonneg h4] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
          · -- Case where x + 4 < 0
            rw [abs_of_neg (not_le.mp h4)] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
    · -- Case where x + 1 < 0
      rw [abs_of_neg (not_le.mp h1)] at hx
      by_cases h2 : x + 2 >= 0
      · -- Case where x + 2 >= 0
        rw [abs_of_nonneg h2] at hx
        by_cases h3 : x + 3 >= 0
        · -- Case where x + 3 >= 0
          rw [abs_of_nonneg h3] at hx
          by_cases h4 : x + 4 >= 0
          · -- Case where x + 4 >= 0
            rw [abs_of_nonneg h4] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
          · -- Case where x + 4 < 0
            rw [abs_of_neg (not_le.mp h4)] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
        · -- Case where x + 3 < 0
          rw [abs_of_neg (not_le.mp h3)] at hx
          by_cases h4 : x + 4 >= 0
          · -- Case where x + 4 >= 0
            rw [abs_of_nonneg h4] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
          · -- Case where x + 4 < 0
            rw [abs_of_neg (not_le.mp h4)] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
      · -- Case where x + 2 < 0
        rw [abs_of_neg (not_le.mp h2)] at hx
        by_cases h3 : x + 3 >= 0
        · -- Case where x + 3 >= 0
          rw [abs_of_nonneg h3] at hx
          by_cases h4 : x + 4 >= 0
          · -- Case where x + 4 >= 0
            rw [abs_of_nonneg h4] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
          · -- Case where x + 4 < 0
            rw [abs_of_neg (not_le.mp h4)] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
        · -- Case where x + 3 < 0
          rw [abs_of_neg (not_le.mp h3)] at hx
          by_cases h4 : x + 4 >= 0
          · -- Case where x + 4 >= 0
            rw [abs_of_nonneg h4] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith
          · -- Case where x + 4 < 0
            rw [abs_of_neg (not_le.mp h4)] at hx
            by_cases h5 : x + 5 >= 0
            · -- Case where x + 5 >= 0
              rw [abs_of_nonneg h5] at hx
              linarith
            · -- Case where x + 5 < 0
              rw [abs_of_neg (not_le.mp h5)] at hx
              linarith