import Mathlib

theorem number_theory_22781 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 3 ∣ n ∧ (Nat.digits 10 n).length = 2 ∧ (Nat.digits 10 n).toFinset.card = 2 ∧ (Nat.digits 10 n).toFinset ⊆ {2, 3, 5, 7, 9}} = 6 := by
  have h : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 3 ∣ n ∧ (Nat.digits 10 n).length = 2 ∧ (Nat.digits 10 n).toFinset.card = 2 ∧ (Nat.digits 10 n).toFinset ⊆ {2, 3, 5, 7, 9}} = Finset.filter (fun x => 3 ∣ x ∧ (Nat.digits 10 x).length = 2 ∧ (Nat.digits 10 x).toFinset.card = 2 ∧ (Nat.digits 10 x).toFinset ⊆ {2, 3, 5, 7, 9}) (Finset.Icc 10 99) := by
    ext n
    simp 
    <;> tauto
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide