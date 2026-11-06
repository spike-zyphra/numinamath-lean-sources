import Mathlib

theorem number_theory_11182 :
    IsGreatest {n | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).sum = 16} 9700 := by 
  constructor
  · -- Show 9700 is in the set
    constructor
    · -- Show 9700 ∈ [1000, 9999]
      native_decide
    · -- Show (Nat.digits 9700).sum = 16
      native_decide
  · -- Show if n in the set, then n ≤ 9700
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    -- Assume n > 9700, computing digit sum.
    -- If n > 9700, then n is from 9701 to 9999.
    have h4 : (Nat.digits 10 n).sum = 16 := hn2
    have h3 : n > 9700 := h
    have h5 : (Nat.digits 10 n).sum > 16 := by 
      have h6 : n ≥ 9701 := by omega
      by_cases h7 : n < 9800
      · -- 9701 ≤ n < 9800
        interval_cases n <;> norm_num at h4 ⊢
      · -- 9800 ≤ n ≤ 9999
        have h8 : n ≥ 9800 := by omega
        have h9 : n < 10000 := by linarith
        interval_cases n <;> norm_num at h4 ⊢
    linarith