import Mathlib

theorem algebra_154442 : IsLeast {x | ∃ a : ℝ, x = a ^ 2 - 2 * a} (-1) := by
  constructor
  · -- Show that -1 is in the set
    use 1
    norm_num
  · -- Show that -1 is the smallest
    intro x
    rintro ⟨a, ha⟩
    have h : a ^ 2 - 2 * a ≥ -1 := by
      have h1 : (a - 1) ^ 2 ≥ 0 := by
        apply sq_nonneg
      linarith
    linarith [ha, h]