import Mathlib

theorem number_theory_107546 :
    IsGreatest {x | 100 ≤ x ∧ x < 1000 ∧ Even x ∧ x % 5 = 2 ∧ Nat.gcd 30 (Nat.gcd x 15) = 3} 972 := by
  constructor
  · -- Show that 972 is in the set
    show 100 ≤ 972 ∧ 972 < 1000 ∧ Even 972 ∧ 972 % 5 = 2 ∧ Nat.gcd 30 (Nat.gcd 972 15) = 3
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · decide
    constructor
    · norm_num
    · norm_num [Nat.gcd, Nat.even_iff]
  · -- Show that 972 is the greatest element in the set
    intro x hx
    rcases hx with ⟨hx1, hx2, hxeven, hx5, hGCD⟩
    by_contra h
    push_neg at h
    interval_cases x <;> norm_num [Nat.even_iff, Nat.gcd] at hGCD ⊢ <;> all_goals contradiction