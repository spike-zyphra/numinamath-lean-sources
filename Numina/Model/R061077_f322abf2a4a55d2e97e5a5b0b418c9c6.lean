import Mathlib

theorem number_theory_5346 :
    IsLeast {x : ℕ | x ≥ 100 ∧ x ≡ 1 [MOD 3] ∧ x ≡ 6 [MOD 7] ∧ x ≡ 4 [MOD 11]} 202 := by
  constructor
  · -- Show 202 is in the set.
    constructor
    · -- 202 ≥ 100.
      norm_num
    constructor
    · -- 202 ≡ 1 (mod 3).
      norm_num [Nat.ModEq]
    constructor
    · -- 202 ≡ 6 (mod 7).
      norm_num [Nat.ModEq]
    · -- 202 ≡ 4 (mod 11).
      norm_num [Nat.ModEq]
  · -- Show there is no smaller element in the set.
    intro x hx
    rcases hx with ⟨hx1, hx2, hx3, hx4⟩
    by_contra h
    push_neg at h
    interval_cases x <;> norm_num [Nat.ModEq] at hx2 hx3 hx4 <;> all_goals
      omega