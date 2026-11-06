import Mathlib

theorem number_theory_23002 :
    IsLeast {n : ℕ | 0 < n ∧ (617 * n ≡ 943 * n [MOD 18])} 9 := by
  constructor
  · -- Show 9 is positive and satisfies the congruence
    show 0 < 9 ∧ (617 * 9 ≡ 943 * 9 [MOD 18])
    constructor
    · norm_num
    · norm_num [Nat.ModEq]
  · -- Show no positive integer less than 9 satisfies the congruence
    intro n hn
    rcases hn with ⟨hn_pos, hn_cong⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.ModEq] at hn_cong <;> omega