import Mathlib

theorem algebra_3873 :
  IsLeast {x | ∃ a b : ℝ, x = a^2 + b^2 + 6*a + 8*b + 2023} 1998 := by
  constructor
  · -- Show 1998 is in the set
    use -3, -4
    norm_num
  · -- Show no number less than 1998 is in the set
    intro x hx
    rcases hx with ⟨a, b, h_eq⟩
    have h : a^2 + b^2 + 6*a + 8*b + 2023 ≥ 1998 := by
      nlinarith [sq_nonneg (a + 3), sq_nonneg (b + 4)]
    linarith [h_eq, h]