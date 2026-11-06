import Mathlib

theorem algebra_21960 :
    IsLeast {x | ∃ a b c : ℝ, x = 2 * a ^ 2 + 3 * b ^ 2 + 6 * c ^ 2 ∧ a + b + c = 1} 1 := by
  constructor
  -- Show that 1 is attained
  · use 1 / 2, 1 / 3, 1 / 6
    constructor
    · norm_num
    · norm_num
  -- Show that 1 is a lower bound
  · intro x hx
    rcases hx with ⟨a, b, c, hx_eq, heq⟩
    have h1 : 2 * a ^ 2 + 3 * b ^ 2 + 6 * c ^ 2 ≥ 1 := by
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 6),
        heq
      ]
    linarith [hx_eq, h1]