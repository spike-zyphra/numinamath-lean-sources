import Mathlib

theorem number_theory_5057 :
    IsLeast {x : ℕ | x ∈ Finset.Icc 1000 9999 ∧ 3 * x ≡ 17 [MOD 19] ∧ 5 * x ≡ 27 [MOD 29] ∧ 7 * x ≡ 2 [MOD 11]} 1380 := by
  constructor
  · -- Verify 1380 is in the set.
    constructor
    · -- Show 1380 is in the interval [1000, 9999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Verify 3*1380 ≡ 17 [MOD 19]
      norm_num [Nat.ModEq]
    constructor
    · -- Verify 5*1380 ≡ 27 [MOD 29]
      norm_num [Nat.ModEq]
    · -- Verify 7*1380 ≡ 2 [MOD 11]
      norm_num [Nat.ModEq]

  · -- Show there is no smaller element in the set
    intro y hy
    rcases hy with ⟨hy1, hy2, hy3, hy4⟩
    rw [Finset.mem_Icc] at hy1
    rcases hy1 with ⟨hy1l, hy1u⟩

    by_contra h
    push_neg at h
    interval_cases y <;> norm_num [Nat.ModEq] at hy2 hy3 hy4 <;> all_goals omega