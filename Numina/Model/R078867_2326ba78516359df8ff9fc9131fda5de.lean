import Mathlib

theorem number_theory_316259 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = n + 4725} = 28 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = n + 4725} = Finset.filter (fun n => (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = n + 4725) (Finset.Icc 1000 9999) := by
    ext n
    simp 
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide