import Mathlib

theorem algebra_22161 :
    IsLeast {p | ∃(a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b^2 + c^3 = 325 / 9 ∧ p = a^2 + b^3 + c^4} (2807 / 27) := by
  constructor
  · -- Show that 2807/27 is in the set.
    use 2, 8 / 3, 3
    constructor
    · norm_num -- 0 < (2 : ℝ)
    constructor
    · norm_num -- 0 < (8 / 3 : ℝ)
    constructor
    · norm_num -- 0 < (3 : ℝ)
    constructor
    · norm_num -- 2 + (8 / 3) ^ 2 + 3 ^ 3 = 325 / 9
    · norm_num -- 2807 / 27 = 2 ^ 2 + (8 / 3) ^ 3 + 3 ^ 4
  · -- Show that 2807/27 is the minimum.
    intro p hp
    rcases hp with ⟨a, b, c, ha, hb, hc, h1, hp⟩
    have h2 : a ^ 2 + b ^ 3 + c ^ 4 ≥ 2807 / 27 := by
      nlinarith [sq_nonneg (a - 2 : ℝ), sq_nonneg (b - 8 / 3 : ℝ), sq_nonneg (c - 3 : ℝ),
        sq_nonneg (a ^ 2 - 4 : ℝ), sq_nonneg (b ^ 2 - 64 / 9 : ℝ), sq_nonneg (c ^ 2 - 9 : ℝ),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (b - 8 / 3 : ℝ), sq_nonneg (c - 3 : ℝ)]
    linarith -- from `p = a^2 + b^3 + c^4` and `a^2 + b^3 + c^4 ≥ 2807/27` to `p ≥ 2807/27`