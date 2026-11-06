import Mathlib

theorem number_theory_254049 :
    Set.ncard {n : ℕ | n > 10 ∧ n < 100 ∧ (Nat.digits 10 n).length = 2 ∧
      (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = n + 9} = 8 := by
  have h1 : {n : ℕ | n > 10 ∧ n < 100 ∧ (Nat.digits 10 n).length = 2 ∧
      (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = n + 9} = Finset.filter (fun n => 
      n > 10 ∧ n < 100 ∧ (Nat.digits 10 n).length = 2 ∧
      (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = n + 9) (Finset.Icc 0 100) := by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide