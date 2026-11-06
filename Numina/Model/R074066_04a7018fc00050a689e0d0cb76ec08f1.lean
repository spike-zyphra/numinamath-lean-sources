import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_296366 (a b c : ℝ) (h : a + b + c = 1) :
    IsLeast {x | ∃ a b c : ℝ, a + b + c = 1 ∧ x = max (max (a + b) (b + c)) (c + a)} (2 / 3) := by
  constructor
  · -- Show that 2/3 is in the set.
    use 1 / 3, 1 / 3, 1 / 3
    constructor
    · norm_num
    · norm_num [max_eq_left, max_eq_right]
  · -- Now we prove that 2/3 is the least element in the set
    rintro x hx
    rcases hx with ⟨a, b, c, h_eq, hx_eq⟩
    have h1 : max (max (a + b) (b + c)) (c + a) ≥ 2 / 3 := by
      by_cases h2 : a + b ≥ b + c
      · -- If a + b ≥ b + c, then max (a + b) (b + c) = a + b
        rw [max_eq_left h2]
        by_cases h3 : a + b ≥ c + a
        · -- If a + b ≥ c + a, then max (a + b) (c + a) = a + b
          rw [max_eq_left h3]
          linarith
        · -- If a + b < c + a, then max (a + b) (c + a) = c + a
          rw [max_eq_right (le_of_not_le h3)]
          linarith
      · -- If a + b < b + c, then max (a + b) (b + c) = b + c
        rw [max_eq_right (le_of_not_le h2)]
        by_cases h4 : b + c ≥ c + a
        · -- If b + c ≥ c + a, then max (b + c) (c + a) = b + c
          rw [max_eq_left h4]
          linarith
        · -- If b + c < c + a, then max (b + c) (c + a) = c + a
          rw [max_eq_right (le_of_not_le h4)]
          linarith
    linarith [h1, hx_eq]