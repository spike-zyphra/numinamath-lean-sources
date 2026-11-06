import Mathlib

theorem inequalities_13533 :
    Set.ncard {p : ℤ × ℤ | p.1 < 0 ∧ p.2 < 0 ∧ p.1 + p.2 > -20} = 171 := by 
  have h1 : {p : ℤ × ℤ | p.1 < 0 ∧ p.2 < 0 ∧ p.1 + p.2 > -20} = Finset.filter (fun s => s.1 < 0 ∧ s.2 < 0 ∧ s.1 + s.2 > -20) (Finset.Icc (-20 : ℤ) 0 ×ˢ Finset.Icc (-20 : ℤ) 0) := by
    ext ⟨a, b⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide