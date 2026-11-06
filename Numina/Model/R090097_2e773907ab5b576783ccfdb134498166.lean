import Mathlib

theorem algebra_2926 : IsLeast {x : ℝ | ∃ a b, x = a^2 + 2*a*b + b^2 - 2*a - 2*b} (-1) := by
  constructor
  · -- Show that -1 is in the set
    use 1 / 2, 1 / 2
    norm_num
  · -- Show that -1 is the smallest element in the set
    intro x hx
    rcases hx with ⟨a, b, h⟩
    have eq1 : a^2 + 2*a*b + b^2 - 2*a - 2*b = (a + b - 1) ^ 2 - 1 := by
      ring
    rw [eq1] at h
    have h1 : (a + b - 1) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith