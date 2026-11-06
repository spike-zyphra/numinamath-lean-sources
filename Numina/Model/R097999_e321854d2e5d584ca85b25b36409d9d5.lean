import Mathlib

theorem number_theory_129641 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ 11 ∣ (n / 100 + n % 100)} = 8181 := by
  have h : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ 11 ∣ (n / 100 + n % 100)} = Finset.filter (fun n => 11 ∣ (n / 100 + n % 100)) (Finset.Icc 10000 99999) := by
    ext n
    simp
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide