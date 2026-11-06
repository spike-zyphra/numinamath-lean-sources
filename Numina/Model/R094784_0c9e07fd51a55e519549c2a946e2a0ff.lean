import Mathlib

theorem algebra_205442 : IsLeast {n : ℝ | ∃ x, n = abs (x + 1) + abs (x - 2) + abs (x - 3)} 4 := by 
  constructor 
  · -- Show that 4 is achievable 
    use 2 
    norm_num [abs_of_nonneg, abs_of_nonpos] 
  · -- Show that no value less than 4 is in the set 
    intro n hn 
    rcases hn with ⟨x, hx⟩ 
    have h : abs (x + 1) + abs (x - 2) + abs (x - 3) ≥ 4 := by 
      by_cases h1 : x + 1 ≥ 0 
      · -- Case x + 1 ≥ 0 
        by_cases h2 : x - 2 ≥ 0 
        · -- Case x - 2 ≥ 0 
          by_cases h3 : x - 3 ≥ 0 
          · -- Case x - 3 ≥ 0, so x ≥ 3 
            rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3] 
            linarith 
          · -- Case x - 3 < 0, so 2 ≤ x < 3 
            rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_neg (lt_of_not_ge h3)] 
            linarith 
        · -- Case x - 2 < 0, so -1 ≤ x < 2 
          by_cases h3 : x - 3 ≥ 0 
          · -- Case x - 3 ≥ 0, impossible 
            rw [abs_of_nonneg h1, abs_of_neg (lt_of_not_ge h2), abs_of_nonneg h3] 
            linarith 
          · -- Case x - 3 < 0, so -1 ≤ x < 2 
            rw [abs_of_nonneg h1, abs_of_neg (lt_of_not_ge h2), abs_of_neg (lt_of_not_ge h3)] 
            linarith 
      · -- Case x + 1 < 0, so x < -1 
        by_cases h2 : x - 2 ≥ 0 
        · -- Case x - 2 ≥ 0, impossible 
          rw [abs_of_neg (lt_of_not_ge h1), abs_of_nonneg h2] 
          all_goals 
          linarith 
          all_goals 
          linarith 
        · -- Case x - 2 < 0, so x < -1 
          by_cases h3 : x - 3 ≥ 0 
          · -- Case x - 3 ≥ 0, impossible 
            rw [abs_of_neg (lt_of_not_ge h1), abs_of_neg (lt_of_not_ge h2), abs_of_nonneg h3] 
            all_goals 
            linarith 
          · -- Case x - 3 < 0, so x < -1 
            rw [abs_of_neg (lt_of_not_ge h1), abs_of_neg (lt_of_not_ge h2), abs_of_neg (lt_of_not_ge h3)] 
            linarith 
    linarith