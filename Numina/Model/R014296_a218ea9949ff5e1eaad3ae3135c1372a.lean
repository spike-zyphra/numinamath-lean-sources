import Mathlib

theorem number_theory_277581 :
    Set.ncard {n : ℕ | 10000 ≤ n ∧ n < 100000 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ 18 ∣ n} = 44 := by
  have h1 : {n : ℕ | 10000 ≤ n ∧ n < 100000 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ 18 ∣ n} = Finset.filter (fun n => 10000 ≤ n ∧ n < 100000 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ 18 ∣ n) (Finset.Iio 100000) := by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide