import Mathlib

theorem algebra_17179 :
    {n | n ∈ Finset.Icc 66 99 ∧ Odd (n / 10) ∧ Even (n % 10)}.ncard = 10 := by 
  have h1 : {n | n ∈ Finset.Icc 66 99 ∧ Odd (n / 10) ∧ Even (n % 10)} = Finset.filter (fun n => Odd (n / 10) ∧ Even (n % 10)) (Finset.Icc 66 99) := by 
    ext n 
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide