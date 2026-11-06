import Mathlib

theorem number_theory_16776 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ n % 10 = 5 ∧ 15 ∣ n} = 30 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ n % 10 = 5 ∧ 15 ∣ n} = Finset.filter (fun n => n % 10 = 5 ∧ 15 ∣ n) (Finset.Icc 100 999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide