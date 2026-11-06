import Mathlib

theorem algebra_4072 :
    (Finset.Icc 1 5).card * (Finset.Icc 1 5).card = 25 ∧
    {(x, y) : ℕ × ℕ | x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ x + y < x * y}.ncard = 15 := by
  constructor
  · -- Show that total number of pairs is 25
    simp
  · -- Show that the number of satisfying pairs is 15
    have : {(x, y) : ℕ × ℕ | x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ x + y < x * y} = Finset.filter (fun p => (p.1 + p.2 < p.1 * p.2)) (Finset.Icc 1 5 ×ˢ Finset.Icc 1 5) := by
      ext ⟨x, y⟩
      simp [Finset.mem_Icc]
      <;> tauto
    rw [this]
    rw [Set.ncard_coe_Finset]
    native_decide