import Mathlib

theorem number_theory_279441 : {x : ℕ | Even x ∧ x ∈ Finset.Icc 1 103}.ncard = {x : ℕ | Odd x ∧ x ∈ Finset.Icc 4 106}.ncard := by
  have h1 : {x : ℕ | Even x ∧ x ∈ Finset.Icc 1 103} = Finset.filter (λ x => Even x) (Finset.Icc 1 103) := by
    ext x
    simp [Nat.even_iff]
    <;> omega

  have h2 : {x : ℕ | Odd x ∧ x ∈ Finset.Icc 4 106} = Finset.filter (λ x => Odd x) (Finset.Icc 4 106) := by
    ext x
    simp [Nat.odd_iff]
    <;> omega

  rw [h1, h2]
  rw [Set.ncard_coe_Finset]
  rw [Set.ncard_coe_Finset]
  native_decide