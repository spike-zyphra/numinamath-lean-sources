import Mathlib

theorem number_theory_59454 :
    {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ ∀ k ∈ Finset.Icc 2 9, n % k = 1}.ncard = 3 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ ∀ k ∈ Finset.Icc 2 9, n % k = 1} = 
      Finset.filter (fun n => ∀ k ∈ Finset.Icc 2 9, n % k = 1) (Finset.Icc 1000 9999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide