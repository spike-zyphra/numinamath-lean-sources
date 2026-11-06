import Mathlib

theorem number_theory_8346 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ 5 ∣ n ∧ n % 100000 = n ∧ (n / 10000) % 10 = n % 10 ∧ 5 ∣ (Nat.digits 10 n).sum} = 200 := by
  have : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ 5 ∣ n ∧ n % 100000 = n ∧ (n / 10000) % 10 = n % 10 ∧ 5 ∣ (Nat.digits 10 n).sum} = Finset.filter (fun n => 5 ∣ n ∧ n % 100000 = n ∧ (n / 10000) % 10 = n % 10 ∧ 5 ∣ (Nat.digits 10 n).sum) (Finset.Icc 10000 99999) := by
    ext n
    simp
    <;> omega
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide