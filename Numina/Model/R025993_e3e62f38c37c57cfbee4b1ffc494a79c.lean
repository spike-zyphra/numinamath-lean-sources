import Mathlib

theorem number_theory_4327 :
    (Set.ncard {x : Finset ℕ | x ⊆ Finset.Icc 1 100 ∧ x.card = 2 ∧ 7 ∣ x.prod id}) / (100 * 99) = 259 / 990 := by
  have h1 : {x : Finset ℕ | x ⊆ Finset.Icc 1 100 ∧ x.card = 2 ∧ 7 ∣ x.prod id} = Finset.filter (fun s => 7 ∣ s.prod id) (Finset.powersetCard 2 (Finset.Icc 1 100)) := by
    ext s
    simp
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide