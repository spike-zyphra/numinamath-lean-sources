import Mathlib

theorem number_theory_135693 : (Set.ncard {x : ℕ | x ∈ Finset.range 2008 ∧ (x + 12) % 6 = 0}) / 2008 = 1 / 6 := by
  have h1 : {x : ℕ | x ∈ Finset.range 2008 ∧ (x + 12) % 6 = 0} = Finset.filter (λ x => (x + 12) % 6 = 0) (Finset.Icc 0 2007) := by
    ext x
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide