import Mathlib

theorem algebra_135499 : IsLeast {s : ℝ | ∃ a b c : ℝ, (0 < a) ∧ (0 < b) ∧ (0 < c) ∧ (a < 1) ∧ (b < 1) ∧ (c < 1) ∧ (a + b + c = 2) ∧ (s = a^2 + b^2 + c^2)} (4 / 3) := by
  constructor
  · -- Show that 4/3 is indeed achievable by setting a = b = c = 2/3
    use 2 / 3, 2 / 3, 2 / 3
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 4/3 is the minimum
    intro s h
    rcases h with ⟨a, b, c, ha, hb, hc, ha1, hb1, hc1, h1, h2⟩
    nlinarith [sq_nonneg (a - 2 / 3), sq_nonneg (b - 2 / 3), sq_nonneg (c - 2 / 3),
      h1, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]