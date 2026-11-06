import Mathlib

theorem number_theory_277127 :
    (Finset.Icc 10 19).card = 10 ∧
    {n | Even n ∧ n ∈ Finset.Icc 10 19}.encard = 5 := by
  constructor
  · -- Show (Finset.Icc 10 19).card = 10
    native_decide
  · -- Show that {n | Even n ∧ n ∈ Finset.Icc 10 19}.encard = 5
    have h : {n | Even n ∧ n ∈ Finset.Icc 10 19} = {10, 12, 14, 16, 18} := by
      ext n
      simp [Finset.mem_Icc, Nat.even_iff]
      constructor
      · -- Forward: if n is even and in range, then n ∈ {10, 12, 14, 16, 18}
        rintro ⟨h_e, ⟨h1, h2⟩⟩
        interval_cases n <;> try tauto
      · -- Backward: if n ∈ {10, 12, 14, 16, 18}, then n is even and in range
        rintro (rfl | rfl | rfl | rfl | rfl)
        · constructor <;> decide
        · constructor <;> decide
        · constructor <;> decide
        · constructor <;> decide
        · constructor <;> decide
    rw [h]
    rw [Set.encard]
    simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
    all_goals linarith