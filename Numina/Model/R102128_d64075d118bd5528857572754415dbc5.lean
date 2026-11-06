import Mathlib

theorem number_theory_6121 (x : ℕ) (hx : 6 * x ≡ 11 [MOD 13]) :
    IsLeast {x | 100 ≤ x ∧ x < 1000 ∧ Even x ∧ 6 * x ≡ 11 [MOD 13]} 108 := by 
  constructor
  · -- Verify that 108 is indeed in the set
    constructor
    · norm_num -- Show that 100 ≤ 108
    constructor
    · norm_num -- Show that 108 < 1000
    constructor
    · decide -- Show that 108 is even
    · -- Verify that 6 * 108 ≡ 11 (mod 13)
      norm_num [Nat.ModEq]
  · -- Now prove minimality of 108
    intro y hy
    rcases hy with ⟨hy1, hy2, hy3, hy4⟩
    -- The element y is in the set, which means it is a three-digit even number satisfying the congruence
    -- We need to show y >= 108
    by_contra h
    push_neg at h 
    interval_cases y <;> norm_num [Nat.ModEq] at hy4 <;> try contradiction
    <;> norm_num at hy3 <;> all_goals try contradiction