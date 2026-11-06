import Mathlib

theorem number_theory_19176 : IsLeast {x : ℕ | 0 < x ∧ 30 * x ≡ 42 [MOD 47]} 39 := by
  constructor
  · -- Show 39 is in the set
    constructor
    · -- Show 0 < 39
      norm_num
    · -- Show 30 * 39 ≡ 42 [MOD 47]
      norm_num [Nat.ModEq]
  · -- Let x be another element in the set, we need to show that 39 ≤ x
    intro x hx
    rcases hx with ⟨hx_pos, hx_cong⟩
    norm_num [Nat.ModEq] at hx_cong
    omega