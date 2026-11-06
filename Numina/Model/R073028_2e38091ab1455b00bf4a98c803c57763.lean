import Mathlib

theorem number_theory_63881 : IsLeast {x | 0 < x ∧ 2^x ≡ 1 [MOD 5] ∧ 2^x ≡ 1 [MOD 7] ∧ 2^x ≡ 1 [MOD 31]} 60 := by 
  constructor
  · -- Verify 60 satisfies the conditions
    constructor
    · -- Show 60 > 0
      norm_num
    constructor
    · -- Show 2^60 ≡ 1 [MOD 5]
      norm_num [Nat.ModEq]
    constructor
    · -- Show 2^60 ≡ 1 [MOD 7]
      norm_num [Nat.ModEq]
    · -- Show 2^60 ≡ 1 [MOD 31]
      norm_num [Nat.ModEq]
  · -- Now show there's no smaller x
    intro y hy
    rcases hy with ⟨hy_pos, hy_mod5, hy_mod7, hy_mod31⟩
    by_contra h
    push_neg at h
    interval_cases y <;> norm_num [Nat.ModEq] at hy_mod5 hy_mod7 hy_mod31 <;> all_goals omega