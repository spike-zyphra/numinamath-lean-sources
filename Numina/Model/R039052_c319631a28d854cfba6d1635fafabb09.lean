import Mathlib

theorem algebra_22083 : IsLeast {x : ℝ |  x ≠ 0 ∧  x = 2 / x - 1 } (-2) := by
  constructor
  · -- Show that -2 is in the set
    constructor
    · -- Show that -2 ≠ 0
      norm_num
    · -- Show that -2 = 2 / (-2) - 1
      norm_num
  · -- Show that -2 is indeed the smallest
    intro x h
    rcases h with ⟨hx1, hx2⟩
    have h1 : x ≠ 0 := hx1
    have h2 : x = 2 / x - 1 := hx2
    have h3 : x ^ 2 = 2 - x := by
      field_simp [h1] at h2
      linarith
    have h4 : (x + 2) * (x - 1) = 0 := by
      linarith [h3]
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- Case where x + 2 = 0, so x = -2
      linarith
    · -- Case where x - 1 = 0, so x = 1
      linarith