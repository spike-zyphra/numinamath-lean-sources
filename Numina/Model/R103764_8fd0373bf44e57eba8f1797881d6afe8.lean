import Mathlib

theorem number_theory_5838 :
    IsGreatest {x | Odd x ∧ x ∈ Finset.Icc 100 999 ∧ x ≡ 13 [MOD 15]} 973 := by
  constructor
  · -- Show 973 is in the set
    constructor
    · -- 973 is odd
      decide
    constructor
    · -- 973 ∈ Finset.Icc 100 999
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- 973 ≡ 13 [MOD 15]
      norm_num [Nat.ModEq]
  · -- Show the greatest element in the set is 973
    intro x hx
    rcases hx with ⟨hx1, hx2, hx3⟩
    rw [Finset.mem_Icc] at hx2
    rcases hx2 with ⟨hx4, hx5⟩
    norm_num [Nat.ModEq] at hx3
    by_contra h
    push_neg at h
    interval_cases x <;> try { contradiction }
    <;> try { tauto }