import Mathlib

theorem number_theory_286441 :
  {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).sum = 20 ∧ 
   Even (n - 16) ∧
   ∃ k, k ∈ Finset.Icc 100 999 ∧ (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = k ∧ k = (n - 16) / 2} =
  {974} := by 
  ext n 
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, we verify that n = 974 satisfies all the conditions
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, hsum, heven, ⟨k, ⟨hk1, hk2⟩, h₁, hk⟩⟩
    have eq3 : n ≤ 999 := by 
      omega 
    have h3 : n = 974 := by 
      have h8 : n ≤ 999 := by
        omega 
      have h9 : n ≥ 100 := by 
        omega 
      interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at hsum h₁ 
      <;> omega 
    linarith 
  · -- Backward implication: n = 974 implies all the conditions
    intro h 
    rw [h]
    constructor 
    · -- Show n is in the range [100, 999]
      norm_num 
    constructor 
    · -- Show the sum of digits is 20 
      norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]
    constructor 
    · -- Show that n - 16 is even 
      native_decide 
    · -- Show the existence of k 
      use 479 
      all_goals 
        norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]