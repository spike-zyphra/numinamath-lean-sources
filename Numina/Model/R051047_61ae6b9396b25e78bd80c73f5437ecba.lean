import Mathlib

open Real Set

theorem algebra_13959 :
    IsLeast {x | ∃ t : ℝ, x = abs (t + 1) + 2 * abs (t - 5) + abs (2 * t - 7) + abs ((t - 11) / 2)} (45 / 4) := by
  constructor
  · -- Show that 45/4 is achievable by choosing t = 7/2
    use 7 / 2
    norm_num [abs_of_nonneg, abs_of_nonpos, mul_div_cancel₀]
  · -- Show that 45/4 is a lower bound
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : abs (t + 1) + 2 * abs (t - 5) + abs (2 * t - 7) + abs ((t - 11) / 2) ≥ 45 / 4 := by
      by_cases h1 : t + 1 ≥ 0
      · -- Case where |t + 1| = t + 1
        rw [abs_of_nonneg h1]
        by_cases h2 : t - 5 ≥ 0
        · -- Case where 2|t - 5| = 2(t - 5)
          rw [abs_of_nonneg h2]
          by_cases h3 : 2 * t - 7 ≥ 0
          · -- Case where |2t - 7| = 2t - 7
            rw [abs_of_nonneg h3]
            by_cases h4 : (t - 11) / 2 ≥ 0
            · -- Case where |(t - 11)/2| = (t - 11)/2
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |(t - 11)/2| = - (t - 11)/2
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where |2t - 7| = -(2t - 7)
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : (t - 11) / 2 ≥ 0
            · -- Case where |(t - 11)/2| = (t - 11)/2
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |(t - 11)/2| = - (t - 11)/2
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
        · -- Case where 2|t - 5| = 2(5 - t)
          rw [abs_of_neg (lt_of_not_ge h2)]
          by_cases h3 : 2 * t - 7 ≥ 0
          · -- Case where |2t - 7| = 2t - 7
            rw [abs_of_nonneg h3]
            by_cases h4 : (t - 11) / 2 ≥ 0
            · -- Case where |(t - 11)/2| = (t - 11)/2
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |(t - 11)/2| = - (t - 11)/2
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where |2t - 7| = -(2t - 7)
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : (t - 11) / 2 ≥ 0
            · -- Case where |(t - 11)/2| = (t - 11)/2
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |(t - 11)/2| = - (t - 11)/2
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
      · -- Case where |t + 1| = -(t + 1)
        rw [abs_of_neg (lt_of_not_ge h1)]
        by_cases h2 : t - 5 ≥ 0
        · -- Case where 2|t - 5| = 2(t - 5)
          rw [abs_of_nonneg h2]
          by_cases h3 : 2 * t - 7 ≥ 0
          · -- Case where |2t - 7| = 2t - 7
            rw [abs_of_nonneg h3]
            by_cases h4 : (t - 11) / 2 ≥ 0
            · -- Case where |(t - 11)/2| = (t - 11)/2
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |(t - 11)/2| = - (t - 11)/2
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where |2t - 7| = -(2t - 7)
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : (t - 11) / 2 ≥ 0
            · -- Case where |(t - 11)/2| = (t - 11)/2
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |(t - 11)/2| = - (t - 11)/2
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
        · -- Case where 2|t - 5| = 2(5 - t)
          rw [abs_of_neg (lt_of_not_ge h2)]
          by_cases h3 : 2 * t - 7 ≥ 0
          · -- Case where |2t - 7| = 2t - 7
            rw [abs_of_nonneg h3]
            by_cases h4 : (t - 11) / 2 ≥ 0
            · -- Case where |(t - 11)/2| = (t - 11)/2
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |(t - 11)/2| = - (t - 11)/2
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
          · -- Case where |2t - 7| = -(2t - 7)
            rw [abs_of_neg (lt_of_not_ge h3)]
            by_cases h4 : (t - 11) / 2 ≥ 0
            · -- Case where |(t - 11)/2| = (t - 11)/2
              rw [abs_of_nonneg h4]
              linarith
            · -- Case where |(t - 11)/2| = - (t - 11)/2
              rw [abs_of_neg (lt_of_not_ge h4)]
              linarith
    linarith [ht, h1]