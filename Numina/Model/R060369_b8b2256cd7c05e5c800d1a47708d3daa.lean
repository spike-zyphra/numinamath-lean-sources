import Mathlib

theorem number_theory_5400 :
    Set.ncard {p : ℕ | p.Prime ∧ p ≤ 100} = 25 := by
  have h : {p : ℕ | p.Prime ∧ p ≤ 100} = Finset.filter (λ x => x.Prime) (Finset.Iic 100) := by
    ext p
    simp
    <;> tauto
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide