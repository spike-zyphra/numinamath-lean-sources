import Mathlib

theorem number_theory_95050 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).length = 3 ∧
      (Nat.digits 10 n).headI ≠ 0 ∧ (Nat.digits 10 n).tail.tail.headI ≠ 0 ∧
      4 ∣ n ∧ 4 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))} = 40 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).length = 3 ∧
    (Nat.digits 10 n).headI ≠ 0 ∧ (Nat.digits 10 n).tail.tail.headI ≠ 0 ∧
    4 ∣ n ∧ 4 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))} = Finset.filter (fun n => 
      (Nat.digits 10 n).length = 3 ∧
      (Nat.digits 10 n).headI ≠ 0 ∧ (Nat.digits 10 n).tail.tail.headI ≠ 0 ∧
      4 ∣ n ∧ 4 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))
    ) (Finset.Icc 100 999) := by 
    ext n
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide