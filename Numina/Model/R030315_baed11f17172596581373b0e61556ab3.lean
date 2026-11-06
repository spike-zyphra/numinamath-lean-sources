import Mathlib

theorem number_theory_176930 :
    {(m, n) : ℕ × ℕ | m ∈ Finset.Icc 10 99 ∧ n ∈ Finset.Icc 10 99 ∧ m + n = 111}.encard = 88 := by
  have h9 : {(m, n) : ℕ × ℕ | m ∈ Finset.Icc 10 99 ∧ n ∈ Finset.Icc 10 99 ∧ m + n = 111} = Finset.filter (fun p : ℕ × ℕ => (p.1 + p.2 = 111)) (Finset.Icc (10 : ℕ) 99 ×ˢ Finset.Icc (10 : ℕ) 99) := by
    ext ⟨m, n⟩
    simp [Finset.mem_Icc]
    <;> tauto
  rw [h9]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide