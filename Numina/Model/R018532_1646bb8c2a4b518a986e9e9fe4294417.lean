import Mathlib

theorem algebra_5922 : IsLeast {y : ℝ | ∃ x, y = x^2 + 14 * x + 85} 36 := by
  constructor
  · -- We will show that 36 belongs to the set by using x = -7
    use -7
    norm_num
  · -- We need to show that 36 is indeed the smallest value
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h : x^2 + 14 * x + 85 ≥ 36 := by
      have h1 : (x + 7) ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith
    linarith [h, hx]