import Mathlib

theorem number_theory_253908 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ 2025 ∣ n ∧ n / 2025 = (Nat.digits 10 n).sum} = 2 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ 2025 ∣ n ∧ n / 2025 = (Nat.digits 10 n).sum} = Finset.filter (fun n => 2025 ∣ n ∧ n / 2025 = (Nat.digits 10 n).sum) (Finset.Icc 10000 99999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide