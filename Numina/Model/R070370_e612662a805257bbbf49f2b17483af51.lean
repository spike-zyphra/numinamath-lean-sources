import Mathlib

/- 3. Find the smallest trimestal number for which all the digits of its triple are even. -/
theorem number_theory_131736 :
    IsLeast {n | n ≥ 100 ∧ ∀ d ∈ Nat.digits 10 (3 * n), Even d} 134 := by
  constructor
  · -- Prove that 134 is in the set
    constructor
    · norm_num -- 134 ≥ 100
    · -- Show that all digits of 3 * 134 = 402 are even
      intro d hd
      norm_num [Nat.digits, Nat.digitsAux] at hd ⊢
      rcases hd with (rfl | rfl | rfl)
      all_goals decide
  · -- Prove that 134 is the smallest
    intro n hn
    have ⟨hn1, hn2⟩ := hn
    by_contra h
    push_neg at h
    -- Assume n < 134, n ≥ 100
    have h2 : n < 134 := by linarith
    interval_cases n <;> norm_num [Nat.even_iff, Nat.digits, Nat.digitsAux] at hn2 ⊢ <;> all_goals tauto