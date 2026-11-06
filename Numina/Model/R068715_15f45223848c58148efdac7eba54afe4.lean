import Mathlib

theorem number_theory_14122 :
    Set.ncard {n : ℕ | ∃ k, n = k^2 ∧ n ∈ Finset.Icc 100 999 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n)} = 3 := by
  have h1 : {n : ℕ | ∃ k, n = k^2 ∧ n ∈ Finset.Icc 100 999 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n)} = {121, 484, 676} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n in the given set
      rintro ⟨k, rfl, ⟨hk1l, hk1r⟩, hk2⟩
      have h2 : k ≤ 31 := by
        nlinarith
      interval_cases k <;> norm_num at *
      <;> simp [Nat.digits, Nat.digitsAux] at hk2 ⊢
      <;> tauto
    · -- Assume n in {121, 484, 676}, prove in the given set
      rintro (rfl | rfl | rfl)
      · -- n = 121
        refine ⟨11, by norm_num, by norm_num, ?_⟩
        native_decide
      · -- n = 484
        refine ⟨22, by norm_num, by norm_num, ?_⟩
        native_decide
      · -- n = 676
        refine ⟨26, by norm_num, by norm_num, ?_⟩
        native_decide
  rw [h1]
  norm_num