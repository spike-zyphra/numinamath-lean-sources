import Mathlib
theorem number_theory_12355 : Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n ≡ 1 [MOD 3]} = 30 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n ≡ 1 [MOD 3]} = Finset.filter (fun n => n ≡ 1 [MOD 3]) (Finset.Icc 10 99) := by
    ext n
    simp [Finset.mem_Icc, Set.mem_setOf_eq]
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide