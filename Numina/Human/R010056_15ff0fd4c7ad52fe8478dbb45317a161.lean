import Mathlib

theorem number_theory_136092 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100000 999999 ∧ 33 ∣ n ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n)} = 300 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 100000 999999 ∧ 33 ∣ n ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n)} = Finset.filter (λ n => 33 ∣ n ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n)) (Finset.Icc 100000 999999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide