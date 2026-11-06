import Mathlib

theorem algebra_318977 (a b : ℝ) :
    IsLeast {x | ∃ a b : ℝ, x = 2*a^2 - 8*a*b + 17*b^2 - 16*a - 4*b + 1990} 1922 := by
  constructor
  · -- Show that 1922 is achievable, i.e., there exist a and b such that P = 1922
    use 8, 2
    norm_num
  · -- Show that 1922 is the least element, i.e., for all x in the set, 1922 ≤ x
    intro x hx
    rcases hx with ⟨a, b, h_eq⟩
    have h : 2 * a ^ 2 - 8 * a * b + 17 * b ^ 2 - 16 * a - 4 * b + 1990 ≥ 1922 := by
      nlinarith [sq_nonneg (a - 2 * b - 4), sq_nonneg (b - 2)]
    linarith [h_eq, h]