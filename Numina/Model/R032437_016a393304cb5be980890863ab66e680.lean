import Mathlib

theorem algebra_11596 : IsLeast {y : ℝ | ∃ x1 x2 x3 : ℝ, 0 < x1 ∧ 0 < x2 ∧ 0 < x3 ∧
    x1 + 2 * x2 + 3 * x3 = 60 ∧ y = x1 ^ 2 + x2 ^ 2 + x3 ^ 2} (1800 / 7) := by
  constructor
  · -- Show 1800/7 is in the set.
    use 30 / 7, 60 / 7, 90 / 7
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
  · -- Show 1800/7 is the smallest
    intro y hy
    rcases hy with ⟨x1, x2, x3, hx1, hx2, hx3, h_eq, hy⟩
    have h1 : x1 + 2 * x2 + 3 * x3 = 60 := h_eq
    have h2 : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≥ 1800 / 7 := by
      nlinarith [sq_nonneg (x1 - 30 / 7), sq_nonneg (x2 - 60 / 7), sq_nonneg (x3 - 90 / 7),
                h_eq, mul_pos hx1 hx2, mul_pos hx2 hx3, mul_pos hx1 hx3]
    linarith [hy, h2]