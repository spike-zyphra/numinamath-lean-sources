import Mathlib

theorem algebra_14531 (y : ℝ) :
    IsLeast {y | 3 * y ^ 2 + 5 * y + 2 = 4} (-2) := by
  constructor
  · -- Show that -2 is in the set.
    norm_num 
  · -- Show that -2 is the least element in the set.
    intro y
    intro hy
    have h_eq : 3 * y ^ 2 + 5 * y + 2 = 4 := by 
      simpa using hy 
    have h_eq2 : 3 * y ^ 2 + 5 * y - 2 = 0 := by 
      linarith 
    have : (3 * y - 1) * (y + 2) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.1 this) with h1 h2
    · -- Case 3 * y - 1 = 0.
      linarith 
    · -- Case y + 2 = 0.
      linarith