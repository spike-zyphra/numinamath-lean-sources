import Mathlib

theorem number_theory_154984 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100000 999999 ∧
      (Nat.digits 10 n).length = 6 ∧
      (Nat.digits 10 n).headI > 0 ∧
      (Nat.digits 10 n).tail.headI > 0 ∧
      (Nat.digits 10 n).tail.tail.headI > 0 ∧
      (Nat.digits 10 n).tail.tail.tail.headI > 0 ∧
      (Nat.digits 10 n).tail.tail.tail.tail.headI > 0 ∧
      (Nat.digits 10 n).tail.tail.tail.tail.tail.headI > 0 ∧
      4 ∣ (Nat.digits 10 n).headI ∧
      3 ∣ (Nat.digits 10 n).tail.headI ∧
      3 ∣ (Nat.digits 10 n).tail.tail.headI ∧
      (Nat.digits 10 n).sum = 21} = 126 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 100000 999999 ∧
    (Nat.digits 10 n).length = 6 ∧
    (Nat.digits 10 n).headI > 0 ∧
    (Nat.digits 10 n).tail.headI > 0 ∧
    (Nat.digits 10 n).tail.tail.headI > 0 ∧
    (Nat.digits 10 n).tail.tail.tail.headI > 0 ∧
    (Nat.digits 10 n).tail.tail.tail.tail.headI > 0 ∧
    (Nat.digits 10 n).tail.tail.tail.tail.tail.headI > 0 ∧
    4 ∣ (Nat.digits 10 n).headI ∧
    3 ∣ (Nat.digits 10 n).tail.headI ∧
    3 ∣ (Nat.digits 10 n).tail.tail.headI ∧
    (Nat.digits 10 n).sum = 21} = Finset.filter (fun n => 
    (Nat.digits 10 n).length = 6 ∧
    (Nat.digits 10 n).headI > 0 ∧
    (Nat.digits 10 n).tail.headI > 0 ∧
    (Nat.digits 10 n).tail.tail.headI > 0 ∧
    (Nat.digits 10 n).tail.tail.tail.headI > 0 ∧
    (Nat.digits 10 n).tail.tail.tail.tail.headI > 0 ∧
    (Nat.digits 10 n).tail.tail.tail.tail.tail.headI > 0 ∧
    4 ∣ (Nat.digits 10 n).headI ∧
    3 ∣ (Nat.digits 10 n).tail.headI ∧
    3 ∣ (Nat.digits 10 n).tail.tail.headI ∧
    (Nat.digits 10 n).sum = 21
    ) (Finset.Icc 100000 999999) := by
    ext n
    simp
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide