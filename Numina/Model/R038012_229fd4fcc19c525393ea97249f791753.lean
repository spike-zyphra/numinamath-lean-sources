import Mathlib

theorem number_theory_239957 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ ∃ k, n - (Nat.digits 10 n).sum = k ∧ k ∈ Finset.Icc 100 999 ∧
      (Nat.digits 10 k).length = 3 ∧ (Nat.digits 10 k).toFinset.card = 1} = 20 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ ∃ k, n - (Nat.digits 10 n).sum = k ∧ k ∈ Finset.Icc 100 999 ∧
      (Nat.digits 10 k).length = 3 ∧ (Nat.digits 10 k).toFinset.card = 1} = Finset.filter (fun n => 
    let k := n - (Nat.digits 10 n).sum
    k ∈ Finset.Icc 100 999 ∧ 
      (Nat.digits 10 k).length = 3 ∧ 
        (Nat.digits 10 k).toFinset.card = 1 
    ) (Finset.Icc 100 999) := by 
    ext n 
    simp 
    <;> aesop 
    <;> try { tauto } 
  rw [h1] 
  rw [Set.ncard_coe_Finset] 
  native_decide