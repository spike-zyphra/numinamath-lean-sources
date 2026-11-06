import Mathlib

theorem number_theory_188048 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ Nat.digits 10 (2 * n) = List.reverse (Nat.digits 10 (2 * n))} = 20 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ Nat.digits 10 (2 * n) = List.reverse (Nat.digits 10 (2 * n))} = Finset.filter (fun n => Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ Nat.digits 10 (2 * n) = List.reverse (Nat.digits 10 (2 * n))) (Finset.Icc 1000 9999) := by
    ext n
    simp 
    <;> try trivial 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide