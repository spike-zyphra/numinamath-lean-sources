import Mathlib

theorem inequalities_5971 :
    Set.ncard {p : ℤ × ℤ | p.1 < 0 ∧ p.2 < 0 ∧ p.1 + p.2 > -15} = 91 := by
  have h1 : {p : ℤ × ℤ | p.1 < 0 ∧ p.2 < 0 ∧ p.1 + p.2 > -15} = Finset.filter (fun p => p.1 < 0 ∧ p.2 < 0 ∧ p.1 + p.2 > -15) (Finset.Icc (-15 : ℤ) 0 ×ˢ Finset.Icc (-15 : ℤ) 0) := by
    ext ⟨a, b⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide