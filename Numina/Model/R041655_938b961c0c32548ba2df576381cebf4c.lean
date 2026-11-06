import Mathlib

theorem number_theory_123554 : IsGreatest {k | 0 < k ∧ k ≤ 48 ∧ ∏ i ∈ Finset.Icc 1 k, (Nat.floor (i / 7) + 1) ≡ 7 [ZMOD 13]} 45 := by
  constructor 
  · -- Show that 45 is in the set
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    · -- Show that ∏ i ∈ Finset.Icc 1 45, (Nat.floor (i / 7) + 1) ≡ 7 [ZMOD 13]
      native_decide
  · -- Show that no k > 45 is in the set 
    intro k hk 
    rcases hk with ⟨hk_pos, hk_le, hk_prod⟩ 
    by_contra h 
    push_neg at h 
    have hk46 : k ≥ 46 := by omega
    have hk48 : k ≤ 48 := by omega 
    interval_cases k <;> norm_num [Int.ModEq] at hk_prod <;> try { contradiction }