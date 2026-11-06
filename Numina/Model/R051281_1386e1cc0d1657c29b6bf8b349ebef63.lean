import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_215536 (a b c : ℝ) (h : ∀ x : ℝ, |x| ≤ 1 → |a * x^2 + b * x + c| ≤ 100) :
    |a| + |b| + |c| ≤ 300 := by

  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  have h3 := h 0 (by norm_num)
  have h4 := h (1 / 2) (by
    norm_num [abs_le]
  )
  have h5 := h (-1 / 2) (by
    norm_num [abs_le]
  )

  cases' abs_le.mp h1 with h1_neg h1_pos
  cases' abs_le.mp h2 with h2_neg h2_pos
  cases' abs_le.mp h3 with h3_neg h3_pos
  cases' abs_le.mp h4 with h4_neg h4_pos
  cases' abs_le.mp h5 with h5_neg h5_pos

  cases' abs_cases a with ha1 ha1
  · cases' abs_cases b with hb1 hb1
    · cases' abs_cases c with hc1 hc1
      · -- Case where a ≥ 0, b ≥ 0, c ≥ 0
        linarith
      · -- Case where a ≥ 0, b ≥ 0, c < 0
        linarith
    · cases' abs_cases c with hc1 hc1
      · -- Case where a ≥ 0, b < 0, c ≥ 0
        linarith
      · -- Case where a ≥ 0, b < 0, c < 0
        linarith
  · cases' abs_cases b with hb1 hb1
    · cases' abs_cases c with hc1 hc1
      · -- Case where a < 0, b ≥ 0, c ≥ 0
        linarith
      · -- Case where a < 0, b ≥ 0, c < 0
        linarith
    · cases' abs_cases c with hc1 hc1
      · -- Case where a < 0, b < 0, c ≥ 0
        linarith
      · -- Case where a < 0, b < 0, c < 0
        linarith