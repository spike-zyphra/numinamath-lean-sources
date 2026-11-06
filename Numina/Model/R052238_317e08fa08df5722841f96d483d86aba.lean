import Mathlib

theorem number_theory_13304 :
    IsLeast {x : ℕ | x > 0 ∧ x ≡ 2 [MOD 3] ∧ x ≡ 3 [MOD 5] ∧ x ≡ 2 [MOD 7]} 23 := by
  constructor
  · -- Show 23 is in the set
    constructor
    · norm_num
    constructor
    · norm_num [Nat.ModEq]
    constructor
    · norm_num [Nat.ModEq]
    · norm_num [Nat.ModEq]
  · -- Show there is no smaller positive integer in the set
    intro y hy
    rcases hy with ⟨hy_pos, hy1, hy2, hy3⟩
    by_contra h
    push_neg at h
    interval_cases y <;> norm_num [Nat.ModEq] at hy1 hy2 hy3 <;> omega