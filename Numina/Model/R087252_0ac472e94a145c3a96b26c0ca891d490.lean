import Mathlib

theorem number_theory_34804 :
    ∑ n in (Finset.Icc 1000 9999).filter (fun n => (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).headI ≠ 0 ∧ (Nat.digits 10 n).tail.headI ≠ 0 ∧
      (Nat.digits 10 n).tail.tail.headI ≠ 0 ∧ (Nat.digits 10 n).tail.tail.tail.headI ≠ 0 ∧
      (Nat.ofDigits 10 (List.map (fun d => d % 5) (Nat.digits 10 n))) = 1434), n = 67384 := by
  native_decide