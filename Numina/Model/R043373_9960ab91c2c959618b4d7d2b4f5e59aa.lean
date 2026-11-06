import Mathlib

theorem number_theory_22803 : {x : ℤ | x ∈ Finset.Icc (-100) 100 ∧ x ≡ 3 [ZMOD 11]}.ncard = 18 := by
  have : {x : ℤ | x ∈ Finset.Icc (-100) 100 ∧ x ≡ 3 [ZMOD 11]} = 
    Finset.filter (fun (x : ℤ) => x ≡ 3 [ZMOD 11]) (Finset.Icc (-100) 100) := by
    ext x 
    simp
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide