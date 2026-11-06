import Mathlib

theorem algebra_3167 :
    IsLeast {n : ℝ | ∃ x : ℝ, n = |2 * x - 4| + |x + 6| + |3 * x + 9| + |4 * x|} 19 := by
  constructor
  · use 0
    norm_num
  · -- Show that 19 is the least element
    intro n hn
    rcases hn with ⟨x, hx⟩
    have h : |2 * x - 4| + |x + 6| + |3 * x + 9| + |4 * x| ≥ 19 := by
      cases' abs_cases (2 * x - 4) with h1 h1
      · cases' abs_cases (x + 6) with h2 h2
        · cases' abs_cases (3 * x + 9) with h3 h3
          · cases' abs_cases (4 * x) with h4 h4
            · -- Case 1: All non-negative
              linarith
            · -- Case 2: |4x| is negative
              linarith
          · cases' abs_cases (4 * x) with h4 h4
            · -- Case 3: |3x + 9| is negative, |4x| non-negative
              linarith
            · -- Case 4: |3x + 9| and |4x| negative
              linarith
        · cases' abs_cases (3 * x + 9) with h3 h3
          · cases' abs_cases (4 * x) with h4 h4
            · -- Case 5: |x + 6| negative, |3x + 9| non-negative
              linarith
            · -- Case 6: |x + 6| and |4x| negative
              linarith
          · cases' abs_cases (4 * x) with h4 h4
            · -- Case 7: |x + 6| and |3x + 9| negative, |4x| non-negative
              linarith
            · -- Case 8: All negative
              linarith
      · cases' abs_cases (x + 6) with h2 h2
        · cases' abs_cases (3 * x + 9) with h3 h3
          · cases' abs_cases (4 * x) with h4 h4
            · -- Case 9: |2x - 4| negative, others non-negative
              linarith
            · -- Case 10: |2x - 4| and |4x| negative
              linarith
          · cases' abs_cases (4 * x) with h4 h4
            · -- Case 11: |2x - 4| and |3x + 9| negative, |4x| non-negative
              linarith
            · -- Case 12: |2x - 4|, |3x + 9|, |4x| negative
              linarith
        · cases' abs_cases (3 * x + 9) with h3 h3
          · cases' abs_cases (4 * x) with h4 h4
            · -- Case 13: |2x - 4| and |x + 6| negative, |3x + 9| non-negative
              linarith
            · -- Case 14: |2x - 4|, |x + 6|, |4x| negative
              linarith
          · cases' abs_cases (4 * x) with h4 h4
            · -- Case 15: |2x - 4|, |x + 6|, |3x + 9| negative, |4x| non-negative
              linarith
            · -- Case 16: All negative
              linarith
    linarith [h, hx]