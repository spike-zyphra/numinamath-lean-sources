import Mathlib

theorem number_theory_12257 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 3 ∣ n ∧ n % 100 = 23} = 30 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 3 ∣ n ∧ n % 100 = 23} = Finset.filter (fun n => 3 ∣ n ∧ n % 100 = 23) (Finset.Icc 1000 9999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide