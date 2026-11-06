import Mathlib

theorem algebra_13399 : {x : ℤ × ℤ | x.1 ∈ Finset.Icc 1 12 ∧ x.2 ∈ Finset.Icc 1 12 ∧ x.1 ≤ x.2 ∧ x.1 % 6 ≠ x.2 % 6}.ncard = 60 := by 
  have h1 : {x : ℤ × ℤ | x.1 ∈ Finset.Icc 1 12 ∧ x.2 ∈ Finset.Icc 1 12 ∧ x.1 ≤ x.2 ∧ x.1 % 6 ≠ x.2 % 6} = Finset.filter (fun pair => (pair.1 ∈ Finset.Icc 1 12) ∧ (pair.2 ∈ Finset.Icc 1 12) ∧ pair.1 ≤ pair.2 ∧ pair.1 % 6 ≠ pair.2 % 6) (Finset.Icc (-100 : ℤ) 100 ×ˢ Finset.Icc (-100 : ℤ) 100) := by 
    ext ⟨a, b⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide