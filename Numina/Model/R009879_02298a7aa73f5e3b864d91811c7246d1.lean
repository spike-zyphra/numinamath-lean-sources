import Mathlib

theorem number_theory_14632:
  IsGreatest {x:ℤ | x < 0 ∧ 34 * x + 6 ≡ 2 [ZMOD 20]} (-6) := by
  constructor
  · -- First, we need to show that -6 is in the set
    constructor
    · -- Show -6 < 0
      norm_num
    · -- Show 34 * (-6) + 6 ≡ 2 [ZMOD 20]
      norm_num [Int.ModEq]
  · -- Show that -6 is greatest in the set
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    -- Given that 34 * x + 6 ≡ 2 [ZMOD 20], we derived that x ≡ 4 [ZMOD 10]
    -- So x can be written as 10k + 4 for some integer k
    -- Since x < 0, we have 10k + 4 < 0 → k < -0.4, so the largest possible k is k = -1
    -- Then x = 10 * (-1) + 4 = -10 + 4 = -6
    -- Therefore x ≤ -6
    norm_num [Int.ModEq] at hx2
    omega