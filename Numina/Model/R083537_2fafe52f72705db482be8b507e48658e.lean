import Mathlib

theorem number_theory_199461 :
    (Finset.Icc 1 200).card = 200 ∧
    {x | ¬ 6 ∣ x ∧ x ∈ Finset.Icc 1 200}.ncard = 167 := by 
  constructor
  · 
    native_decide
  · 
    have h1 : {x | ¬ 6 ∣ x ∧ x ∈ Finset.Icc 1 200} = Finset.filter (fun x => ¬ 6 ∣ x) (Finset.Icc 1 200) := by
      ext x
      simp 
      <;> tauto 
    rw [h1]
    rw [Set.ncard_coe_Finset]
    native_decide