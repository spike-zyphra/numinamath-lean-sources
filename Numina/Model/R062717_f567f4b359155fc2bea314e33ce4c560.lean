import Mathlib

theorem number_theory_9562 :
    IsGreatest {x : ℕ | x ∈ Finset.Icc 100 999 ∧ x ≡ 11 [MOD 19] ∧ x ≡ 11 [MOD 23]} 885 := by 
  constructor
  · -- First, we'll prove that 885 belongs to the set.
    constructor
    · -- Show that 885 ∈ [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that 885 ≡ 11 [MOD 19]
      norm_num [Nat.ModEq]
    · -- Show that 885 ≡ 11 [MOD 23]
      norm_num [Nat.ModEq]
  · -- Now, prove that 885 is the greatest element in the set.
    intro x hx
    rcases hx with ⟨hx1, hx2, hx3⟩
    rw [Finset.mem_Icc] at hx1
    rcases hx1 with ⟨hx1l, hx1u⟩
    norm_num [Nat.ModEq] at hx2 hx3
    by_contra h
    push_neg at h
    interval_cases x <;> omega