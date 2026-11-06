import Mathlib

theorem number_theory_228889 :
    {n : ℕ | n ∈ Finset.Icc 10 99 ∧ ∃ k : ℕ, n^2 = k ∧ k ∈ Finset.Icc 1000 9999 ∧ 
    (Nat.digits 10 k).headI = (Nat.digits 10 k).tail.headI ∧ 
    (Nat.digits 10 k).tail.tail.headI = (Nat.digits 10 k).tail.tail.tail.headI} = {88} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Forward implication: need to show n = 88
    rintro ⟨⟨hn1, hn2⟩, ⟨k, h1, h2, h3, h4⟩⟩
    rcases h2 with ⟨hk1, hk2⟩
    have h7 : k = n ^ 2 := by linarith
    rw [h7] at h3 h4
    interval_cases n <;> norm_num [Nat.digits, Nat.digitsAux] at h3 h4 ⊢ 
  · -- Backward implication: need to show 88 is in the set
    intro h
    rw [h]
    constructor
    · -- Show 88 is in the range [10, 99]
      all_goals norm_num
    · -- Show the existence of k
      use 7744
      all_goals norm_num [Nat.digits, Nat.digitsAux]