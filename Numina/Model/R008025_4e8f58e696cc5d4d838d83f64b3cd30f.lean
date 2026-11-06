import Mathlib

theorem algebra_13509 : IsLeast {x | ∃ y : ℝ, x = y^2 + 8 * y} (-16) := by
  constructor
  · -- Show that -16 is in the set
    use -4
    norm_num
  · -- Show that -16 is the least element in the set
    intro x hx
    rcases hx with ⟨y, hy⟩
    have h : y^2 + 8 * y ≥ -16 := by
      nlinarith [sq_nonneg (y + 4)]
    linarith [hy, h]