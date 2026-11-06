import Mathlib

theorem algebra_261833 :
    Set.ncard {p : ℤ × ℤ | p.1 ∈ Finset.Ioo 25 75 ∧ p.2 ∈ Finset.Ioo 120 250 ∧ p.2 = 4 * p.1 + 3} = 32 := by
  have h1 : {p : ℤ × ℤ | p.1 ∈ Finset.Ioo 25 75 ∧ p.2 ∈ Finset.Ioo 120 250 ∧ p.2 = 4 * p.1 + 3} = Finset.filter (fun p : ℤ × ℤ => p.2 ∈ Finset.Ioo 120 250 ∧ p.2 = 4 * p.1 + 3) (Finset.Ioo (25 : ℤ) (75 : ℤ) ×ˢ Finset.Ioo (120 : ℤ) (250 : ℤ)) := by
    ext ⟨x, y⟩
    simp [Finset.mem_Ioo]
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide