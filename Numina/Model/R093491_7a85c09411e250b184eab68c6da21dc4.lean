import Mathlib

theorem number_theory_4152 : ∑ᶠ n ∈ {n : ℕ | 0 < n ∧ n < 2020 ∧ (Nat.digits 10 (9 ^ n)).headI = 9}, n = 1020100 := by
  have h1 : {n : ℕ | 0 < n ∧ n < 2020 ∧ (Nat.digits 10 (9 ^ n)).headI = 9} = Finset.filter (fun n => 0 < n ∧ n < 2020 ∧ (Nat.digits 10 (9 ^ n)).headI = 9) (Finset.Icc 0 2020) := by 
    ext n
    simp
    omega
  rw [h1]
  rw [finsum_mem_coe_finset]
  native_decide