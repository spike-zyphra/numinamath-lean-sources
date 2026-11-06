import Mathlib

theorem algebra_304712 : IsLeast {x : ℝ | ∃ a b, x = a^2 + a * b + b^2 - a - 2 * b} (-1) := by
  constructor
  · -- Show that -1 is attainable, so it's in the set
    use 0, 1
    norm_num
  · -- Show that -1 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, h_eq⟩
    have h : a^2 + a * b + b^2 - a - 2 * b ≥ -1 := by
      nlinarith [sq_nonneg (a + (b - 1) / 2), sq_nonneg (b - 1)]
    linarith [h_eq, h]