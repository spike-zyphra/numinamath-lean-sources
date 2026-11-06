import Mathlib

theorem algebra_318224 : IsLeast {x | ∃ a b : ℝ, x = 2*a^2 + 3*b^2 - 4*a*b - 5*a - 6*b + 7} (-26 - 3/8) := by
  constructor
  · -- Show that -26 - 3/8 is in the set, using a = 27/4 and b = 11/2
    use 27 / 4, 11 / 2
    norm_num
  · -- Show that any x in the set is ≥ -26 - 3/8
    intro x hx
    rcases hx with ⟨a, b, h⟩
    have h1 : 2*a^2 + 3*b^2 - 4*a*b - 5*a - 6*b + 7 ≥ -26 - 3/8 := by
      nlinarith [sq_nonneg (a - b - 5 / 4), sq_nonneg (b - 11 / 2), sq_nonneg (a - 27 / 4), sq_nonneg (b - 11 / 2), sq_nonneg (a - (b + 5 / 4)), sq_nonneg ((a - b) - 5 / 4)]
    linarith