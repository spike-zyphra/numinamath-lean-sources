import Mathlib

theorem number_theory_6404 :
    Set.ncard {n : ℕ | 0 < n ∧ n < 2020 ∧ (Nat.digits 10 n).sum = 5} = 38 := by
  have h1 : {n : ℕ | 0 < n ∧ n < 2020 ∧ (Nat.digits 10 n).sum = 5} = Finset.filter (fun n => 0 < n ∧ n < 2020 ∧ (Nat.digits 10 n).sum = 5) (Finset.Icc 0 2019) := by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide