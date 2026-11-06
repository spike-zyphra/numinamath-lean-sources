import Mathlib
open Mathlib

theorem algebra_3682 : {n : ℕ | ∃ dimes quarters : ℕ, dimes * 10 + quarters * 25 = n ∧ dimes * 5 = quarters * 2 ∧ 300 < n ∧ n < 1000}.encard = 4 := by 
  have h1 : {n : ℕ | ∃ dimes quarters : ℕ, dimes * 10 + quarters * 25 = n ∧ dimes * 5 = quarters * 2 ∧ 300 < n ∧ n < 1000} = {435, 580, 725, 870} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Forward: if n in the set, then n is one of four
      rintro ⟨dimes, quarters, h_eq, h_eq', h_lt₁, h_lt₂⟩
      have h2 : quarters % 5 = 0 := by
        omega
      have h3 : ∃ k, quarters = 5 * k := by 
        refine' ⟨quarters / 5, by omega⟩
      rcases h3 with ⟨k, h_eq3⟩
      have eq_eq : dimes = 2 * k := by
        nlinarith
      have h_eq_total : n = 145 * k := by
        nlinarith [h_eq, h_eq3]
      have h3 : k ≥ 3 := by
        nlinarith
      have h4 : k ≤ 6 := by
        nlinarith
      interval_cases k <;> omega
    · -- Backward: if n is one of four then it's in the set
      rintro (rfl | rfl | rfl | rfl)
      · -- 435
        exact ⟨6, 15, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- 580
        exact ⟨8, 20, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- 725
        exact ⟨10, 25, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- 870
        exact ⟨12, 30, by norm_num, by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { rfl }
  <;> try { norm_num }
  <;> try { aesop }
  <;> try { tauto }
  all_goals try { omega }