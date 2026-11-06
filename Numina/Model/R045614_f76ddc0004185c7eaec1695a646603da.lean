import Mathlib

theorem number_theory_132392 :
    Set.ncard {n : ℕ | 1000 ≤ n ∧ n < 10000 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ 6 ∣ n} = 13 := by 
  have h1 : {n : ℕ | 1000 ≤ n ∧ n < 10000 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ 6 ∣ n} = Finset.filter (fun n => 1000 ≤ n ∧ n < 10000 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ 6 ∣ n) (Finset.Icc 0 9999) := by
    ext n
    simp
    omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide