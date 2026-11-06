import Mathlib

theorem number_theory_280050 : {n : ℕ | n ∈ Finset.Icc 1 99 ∧ Even n ∧ 5 ∣ n}.ncard = 9 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 99 ∧ Even n ∧ 5 ∣ n} = Finset.filter (fun n => Even n ∧ 5 ∣ n) (Finset.Icc 1 99) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide