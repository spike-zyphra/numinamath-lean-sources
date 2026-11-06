import Mathlib

theorem number_theory_7003 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n % 10 < (n / 10) % 10} = 45 := by
  have h2 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n % 10 < (n / 10) % 10} = Finset.filter (fun n => n % 10 < (n / 10) % 10) (Finset.Icc 10 99) := by
    ext n
    simp
  rw [h2]
  rw [Set.ncard_coe_Finset]
  native_decide