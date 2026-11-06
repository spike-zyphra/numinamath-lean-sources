import Mathlib

theorem number_theory_70060 :
    ∃ n, {p | p.Prime ∧ p ∈ Finset.Ioo (n^2) ((n + 1)^2)}.ncard ≥ 1000 := by
  use 14999
  have h1 : {p | p.Prime ∧ p ∈ Finset.Ioo (14999^2) ((14999 + 1)^2)}.ncard ≥ 1000 := by 
    have h2 : {p | p.Prime ∧ p ∈ Finset.Ioo (14999^2) ((14999 + 1)^2)} = Finset.filter (fun p => p.Prime) (Finset.Ioo (14999^2) ((14999 + 1)^2)) := by
      ext p
      simp
      <;> tauto
    rw [h2]
    rw [Set.ncard_coe_Finset]
    native_decide
  exact h1