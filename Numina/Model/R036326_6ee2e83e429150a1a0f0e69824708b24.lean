import Mathlib

theorem algebra_207492 :
    IsLeast {x | ∃ r : ℝ, x = abs (r + 1) + 2 * abs (r - 5) + abs (2 * r - 7) + abs ((r - 11) / 2)} (45 / 4) := by
  constructor
  · -- Show 45/4 is in the set
    use 3.5
    norm_num [abs]
    <;> norm_num
  · -- Show 45/4 is the least
    intro x hx
    rcases hx with ⟨r, hr⟩
    have h1 : abs (r + 1) + 2 * abs (r - 5) + abs (2 * r - 7) + abs ((r - 11) / 2) ≥ 45 / 4 := by
      by_cases h1 : r + 1 ≥ 0
      · -- r + 1 ≥ 0
        rw [abs_of_nonneg h1]
        by_cases h2 : r - 5 ≥ 0
        · -- r - 5 ≥ 0
          rw [abs_of_nonneg (by linarith)]
          by_cases h3 : (2 * r - 7 : ℝ) ≥ 0
          · -- 2 * r - 7 ≥ 0
            rw [abs_of_nonneg (by linarith)]
            by_cases h4 : (r - 11 : ℝ) / 2 ≥ 0
            · -- (r - 11) / 2 ≥ 0
              rw [abs_of_nonneg (by linarith)]
              linarith
            · -- (r - 11) / 2 < 0
              rw [abs_of_neg (by linarith)]
              linarith
          · -- 2 * r - 7 < 0
            rw [abs_of_neg (by linarith)]
            by_cases h4 : (r - 11 : ℝ) / 2 ≥ 0
            · -- (r - 11) / 2 ≥ 0
              rw [abs_of_nonneg (by linarith)]
              linarith
            · -- (r - 11) / 2 < 0
              rw [abs_of_neg (by linarith)]
              linarith
        · -- r - 5 < 0
          rw [abs_of_neg (by linarith)]
          by_cases h3 : (2 * r - 7 : ℝ) ≥ 0
          · -- 2 * r - 7 ≥ 0
            rw [abs_of_nonneg (by linarith)]
            by_cases h4 : (r - 11 : ℝ) / 2 ≥ 0
            · -- (r - 11) / 2 ≥ 0
              rw [abs_of_nonneg (by linarith)]
              linarith
            · -- (r - 11) / 2 < 0
              rw [abs_of_neg (by linarith)]
              linarith
          · -- 2 * r - 7 < 0
            rw [abs_of_neg (by linarith)]
            by_cases h4 : (r - 11 : ℝ) / 2 ≥ 0
            · -- (r - 11) / 2 ≥ 0
              rw [abs_of_nonneg (by linarith)]
              linarith
            · -- (r - 11) / 2 < 0
              rw [abs_of_neg (by linarith)]
              linarith
      · -- r + 1 < 0
        rw [abs_of_neg (by linarith)]
        by_cases h2 : r - 5 ≥ 0
        · -- r - 5 ≥ 0
          rw [abs_of_nonneg (by linarith)]
          by_cases h3 : (2 * r - 7 : ℝ) ≥ 0
          · -- 2 * r - 7 ≥ 0
            rw [abs_of_nonneg (by linarith)]
            by_cases h4 : (r - 11 : ℝ) / 2 ≥ 0
            · -- (r - 11) / 2 ≥ 0
              rw [abs_of_nonneg (by linarith)]
              linarith
            · -- (r - 11) / 2 < 0
              rw [abs_of_neg (by linarith)]
              linarith
          · -- 2 * r - 7 < 0
            rw [abs_of_neg (by linarith)]
            by_cases h4 : (r - 11 : ℝ) / 2 ≥ 0
            · -- (r - 11) / 2 ≥ 0
              rw [abs_of_nonneg (by linarith)]
              linarith
            · -- (r - 11) / 2 < 0
              rw [abs_of_neg (by linarith)]
              linarith
        · -- r - 5 < 0
          rw [abs_of_neg (by linarith)]
          by_cases h3 : (2 * r - 7 : ℝ) ≥ 0
          · -- 2 * r - 7 ≥ 0
            rw [abs_of_nonneg (by linarith)]
            by_cases h4 : (r - 11 : ℝ) / 2 ≥ 0
            · -- (r - 11) / 2 ≥ 0
              rw [abs_of_nonneg (by linarith)]
              linarith
            · -- (r - 11) / 2 < 0
              rw [abs_of_neg (by linarith)]
              linarith
          · -- 2 * r - 7 < 0
            rw [abs_of_neg (by linarith)]
            by_cases h4 : (r - 11 : ℝ) / 2 ≥ 0
            · -- (r - 11) / 2 ≥ 0
              rw [abs_of_nonneg (by linarith)]
              linarith
            · -- (r - 11) / 2 < 0
              rw [abs_of_neg (by linarith)]
              linarith
    linarith [hr, h1]