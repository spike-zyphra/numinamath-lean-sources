import Mathlib

theorem number_theory_287737 :
    Set.ncard {s : Finset ℕ | s ⊆ Finset.Icc 1 100 ∧ s.card = 2 ∧ 7 ∣ ∏ x ∈ s, x + ∑ x ∈ s, x} = 602 := by

  have h1 : {s : Finset ℕ | s ⊆ Finset.Icc 1 100 ∧ s.card = 2 ∧ 7 ∣ ∏ x ∈ s, x + ∑ x ∈ s, x} = Finset.filter (fun s => 7 ∣ ∏ x ∈ s, x + ∑ x ∈ s, x) (Finset.powersetCard 2 (Finset.Icc 1 100)) := by
    ext s
    simp
    <;> tauto

  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide