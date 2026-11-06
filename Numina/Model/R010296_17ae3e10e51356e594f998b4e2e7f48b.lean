import Mathlib

theorem number_theory_12801:
    IsLeast {(x : ℤ) | 1000 ≤ x ∧ x < 10000 ∧ 7 * x ≡ 21 [ZMOD 14] ∧ 2 * x + 13 ≡ 16 [ZMOD 9] ∧ -2 * x + 1 ≡ x [ZMOD 25]} 1167 := by
  constructor
  · -- Show that 1167 is indeed in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num [Int.ModEq]
    constructor
    · norm_num [Int.ModEq]
    · norm_num [Int.ModEq]
  · -- Assume x in the set, prove x >= 1167
    intro x hx
    rcases hx with ⟨hx1, hx2, h1, h2, h3⟩
    by_contra h
    push_neg at h
    interval_cases x <;> norm_num [Int.ModEq] at h1 h2 h3 hx1 hx2 ⊢ <;> omega