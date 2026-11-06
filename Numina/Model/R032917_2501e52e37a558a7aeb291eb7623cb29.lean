import Mathlib

theorem algebra_21657 : IsLeast {x | ∃ a : ℝ, x = a ^ 2 + 6 * a - 7} (-16) := by 
  constructor
  · -- We need to show that -16 is in the set.
    use -3
    norm_num
  · -- We need to show that -16 is the smallest element in the set.
    intro x hx
    rcases hx with ⟨a, ha⟩
    have h1 : a ^ 2 + 6 * a - 7 ≥ -16 := by 
      nlinarith [sq_nonneg (a + 3)]
    linarith [ha, h1]