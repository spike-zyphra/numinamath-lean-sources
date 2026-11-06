import Mathlib

theorem algebra_326915 :
    Set.ncard {(x, y, z) : ℕ × ℕ × ℕ | x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x + y = 3 * z + 10 ∧ x ∈ Finset.Icc 1 100 ∧ y ∈ Finset.Icc 1 100 ∧ z ∈ Finset.Icc 1 100} = 3194 := by
  have : {(x, y, z) : ℕ × ℕ × ℕ | x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x + y = 3 * z + 10 ∧ x ∈ Finset.Icc 1 100 ∧ y ∈ Finset.Icc 1 100 ∧ z ∈ Finset.Icc 1 100} = Finset.filter (fun s : ℕ × ℕ × ℕ => 
    (s.1 ≠ s.2.1) ∧ (s.2.1 ≠ s.2.2) ∧ (s.2.2 ≠ s.1) ∧ (s.1 + s.2.1 = 3 * s.2.2 + 10) ∧ (s.1 ∈ Finset.Icc 1 100) ∧ (s.2.1 ∈ Finset.Icc 1 100) ∧ (s.2.2 ∈ Finset.Icc 1 100)
    ) (Finset.Icc (1 : ℕ) 100 ×ˢ Finset.Icc (1 : ℕ) 100 ×ˢ Finset.Icc (1 : ℕ) 100) := by
    ext ⟨x, y, z⟩
    simp [Finset.mem_Icc]
    <;> tauto 
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide