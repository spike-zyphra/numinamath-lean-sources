import Mathlib

theorem number_theory_2726 :
    IsGreatest {n | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).sum = 34 ∧ 11 ∣ n} 9988 ∧
    IsLeast {n | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).sum = 34 ∧ 11 ∣ n} 8899 := by
  constructor
  · -- Show that 9988 is the greatest element in the set
    constructor
    · -- Show that 9988 is in the set
      refine' ⟨by native_decide, by native_decide, by native_decide⟩
    · -- Show that any n in the set ≤ 9988
      intro n hn
      have h1 : n ∈ {n | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).sum = 34 ∧ 11 ∣ n} := hn
      have h5 : n ∈ (Finset.Icc 1000 9999).filter (fun n => (Nat.digits 10 n).sum = 34 ∧ 11 ∣ n) := by
        simpa using h1
      have h2 : (Finset.Icc 1000 9999).filter (fun n => (Nat.digits 10 n).sum = 34 ∧ 11 ∣ n) = {8899, 8998, 9889, 9988} := by
        native_decide
      have h9 : n ∈ (Finset.Icc 1000 9999).filter (fun n => (Nat.digits 10 n).sum = 34 ∧ 11 ∣ n) := h5
      rw [h2] at h9
      simp [Finset.mem_insert, Finset.mem_singleton] at h9 ⊢
      rcases h9 with (h9 | h9 | h9 | h9)
      all_goals
        norm_num [h9]
  · -- Show that 8899 is the least element in the set
    constructor
    · -- Show that 8899 is in the set
      refine' ⟨by native_decide, by native_decide, by native_decide⟩
    · -- Show that any n in the set ≥ 8899
      intro n hn
      have h1 : n ∈ {n | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).sum = 34 ∧ 11 ∣ n} := hn
      have h9 : n ∈ (Finset.Icc 1000 9999).filter (fun n => (Nat.digits 10 n).sum = 34 ∧ 11 ∣ n) := by 
        simpa using h1
      have h2 : (Finset.Icc 1000 9999).filter (fun n => (Nat.digits 10 n).sum = 34 ∧ 11 ∣ n) = {8899, 8998, 9889, 9988} := by 
        native_decide
      rw [h2] at h9
      simp [Finset.mem_insert, Finset.mem_singleton] at h9 ⊢
      rcases h9 with (h9 | h9 | h9 | h9)
      all_goals
        norm_num [h9]