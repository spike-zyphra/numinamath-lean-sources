import Mathlib

theorem number_theory_234657 :
    Set.ncard {n : ℕ | ∃ m, n ∈ Finset.Icc 100 999 ∧ m ∈ Finset.Icc 100 999 ∧ n - 297 = m ∧ m = Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))} = 60 := by 
  have : {n : ℕ | ∃ m, n ∈ Finset.Icc 100 999 ∧ m ∈ Finset.Icc 100 999 ∧ n - 297 = m ∧ m = Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))} = Finset.filter (fun n => ∃ m, m ∈ Finset.Icc 100 999 ∧ n - 297 = m ∧ m = Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) (Finset.Icc 100 999) := by 
    ext n 
    simp 
    <;> tauto 
  rw [this] 
  rw [Set.ncard_coe_Finset] 
  native_decide