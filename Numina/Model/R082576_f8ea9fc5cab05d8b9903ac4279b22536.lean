import Mathlib

theorem number_theory_6422 :
    IsLeast {x : ℕ | x ∈ Finset.Icc 100 999 ∧ Even x ∧ 4 * x ≡ 11 [MOD 17]} 126 := by 
  constructor 
  · -- Show that 126 belongs to the set
    constructor
    · -- Show 126 is in the range [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩ 
    constructor 
    · -- Show 126 is even
      exact Nat.even_iff.mpr (by norm_num)
    · -- Show 4 * 126 ≡ 11 [MOD 17]
      norm_num [Nat.ModEq]
  · -- Show that 126 is the smallest
    intro y hy 
    rcases hy with ⟨hy1, hy2, hy3⟩
    rw [Finset.mem_Icc] at hy1
    rcases hy1 with ⟨hy1l, hy1u⟩
    by_contra h
    push_neg at h
    interval_cases y <;> try { 
      norm_num [Nat.ModEq] at hy3 
      all_goals 
        try { contradiction }
    }
    all_goals
      try { contradiction }