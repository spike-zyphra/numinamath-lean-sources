import Mathlib

theorem algebra_289067 :
    IsLeast {x | ∃ a b : ℝ, x = 2 * a + b ∧ 3 * abs (a - b) + abs (2 * a - 5) = a + 1} 4 := by
  constructor
  · -- Show that 4 is in the set
    use 4 / 3, 4 / 3
    constructor
    · -- Show that the expression equals 4
      norm_num
    · -- Show that the constraint is satisfied
      norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- We now show that 4 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, hx_eq, h_eq⟩
    by_cases h1 : a - b ≥ 0
    · -- If a - b ≥ 0, then |a - b| = a - b
      rw [abs_of_nonneg h1] at h_eq
      by_cases h2 : 2 * a - 5 ≥ 0
      · -- If 2*a -5 ≥ 0, then |2*a -5| = 2*a -5
        rw [abs_of_nonneg h2] at h_eq
        linarith [h_eq, hx_eq]
      · -- If 2*a -5 < 0, then |2*a -5| = 5 - 2*a
        rw [abs_of_neg (lt_of_not_ge h2)] at h_eq
        linarith [h_eq, hx_eq]
    · -- If a - b < 0, then |a - b| = b - a
      rw [abs_of_neg (lt_of_not_ge h1)] at h_eq
      by_cases h2 : 2 * a - 5 ≥ 0
      · -- If 2*a -5 ≥ 0, then |2*a -5| = 2*a -5
        rw [abs_of_nonneg h2] at h_eq
        linarith [h_eq, hx_eq]
      · -- If 2*a -5 < 0, then |2*a -5| = 5 - 2*a
        rw [abs_of_neg (lt_of_not_ge h2)] at h_eq
        linarith [h_eq, hx_eq]