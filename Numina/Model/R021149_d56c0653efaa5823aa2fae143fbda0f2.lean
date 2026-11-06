import Mathlib

theorem algebra_10505 {x : ℝ} (h : 2*x^2 + 24*x - 60 = x*(x+13)) :
    IsLeast {x | 2*x^2 + 24*x - 60 = x*(x+13)} (-15) := by
  constructor
  · -- Show that -15 is in the set
    norm_num
  · -- Show that -15 is the smallest element in the set
    intro y hy
    have h_eq : 2 * y ^ 2 + 24 * y - 60 = y * (y + 13) := by
      simpa using hy
    -- Rearrange the equation to standard form
    have h_eq2 : y ^ 2 + 11 * y - 60 = 0 := by
      linarith [h_eq]
    -- Factor the quadratic
    have h_eq3 : (y - 4) * (y + 15) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h_eq3) with h1 h2
    · -- Case y - 4 = 0, so y = 4
      linarith
    · -- Case y + 15 = 0, so y = -15
      linarith