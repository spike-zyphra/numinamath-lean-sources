import Mathlib

theorem number_theory_13614 : IsLeast {x : ℕ | x > 0 ∧ 7 * x ≡ 2 [MOD 3] ∧ 3 * x ≡ 2 [MOD 17]} 29 := by
  constructor
  · -- Show 29 is in the set
    constructor
    · -- Show 29 > 0
      norm_num
    constructor
    · -- Show 7 * 29 ≡ 2 [MOD 3]
      norm_num [Nat.ModEq]
    · -- Show 3 * 29 ≡ 2 [MOD 17]
      norm_num [Nat.ModEq]
  · -- Show 29 is the smallest
    intro x hx
    rcases hx with ⟨hx1, hx2, hx3⟩
    by_contra h
    push_neg at h
    interval_cases x <;> norm_num [Nat.ModEq] at hx2 hx3 <;> omega