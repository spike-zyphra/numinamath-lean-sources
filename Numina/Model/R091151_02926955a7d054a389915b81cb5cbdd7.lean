import Mathlib

theorem algebra_20834 : (Finset.Icc 1 100).card = 100 ∧
    {x | 3 ∣ x ∧ x ∈ Finset.Icc 1 100}.ncard = 33 := by
  constructor
  · -- Finset.Icc 1 100 has 100 elements.
    simp
  · -- There are exactly 33 multiples of 3 in Finset.Icc 1 100.
    have h1 : {x | 3 ∣ x ∧ x ∈ Finset.Icc 1 100} = Finset.filter (λ x => 3 ∣ x) (Finset.Icc 1 100) := by
      ext x
      simp
      <;> tauto
    rw [h1]
    rw [Set.ncard_coe_Finset]
    native_decide