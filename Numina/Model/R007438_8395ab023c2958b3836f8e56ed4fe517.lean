import Mathlib

theorem algebra_13551 : IsLeast {n : ℤ | n^2 = 2 * n + 48} (-6) := by
  constructor
  · -- Show that -6 is in the set
    show (-6 : ℤ) ^ 2 = 2 * (-6) + 48
    norm_num
  · -- Show that -6 is the least in the set
    intro n hn
    have h : n ^ 2 = 2 * n + 48 := by
      simpa using hn
    have h1 : n ^ 2 - 2 * n - 48 = 0 := by linarith
    have h2 : (n - 8) * (n + 6) = 0 := by 
      nlinarith [h1]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where n - 8 = 0, so n = 8
      have h5 : n = 8 := by
        linarith
      linarith
    · -- Case where n + 6 = 0, so n = -6
      have h5 : n = -6 := by
        linarith
      linarith