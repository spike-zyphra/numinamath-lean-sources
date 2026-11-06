import Mathlib

theorem algebra_11305 : Set.ncard {(x, y) : ℕ × ℕ | x ∈ Set.Icc 1 6 ∧ y ∈ Set.Icc 1 6 ∧ x < y ∧ x + y ≠ 7} = 12 := by 
  have h1 : {(x, y) : ℕ × ℕ | x ∈ Set.Icc 1 6 ∧ y ∈ Set.Icc 1 6 ∧ x < y ∧ x + y ≠ 7} = Finset.filter (fun s : ℕ × ℕ => (s.1 ≥ 1 ∧ s.1 ≤ 6 ∧ s.2 ≥ 1 ∧ s.2 ≤ 6 ∧ s.1 < s.2 ∧ s.1 + s.2 ≠ 7)) (Finset.Icc (0 : ℕ × ℕ) (6, 6)) := by
    ext ⟨x, y⟩
    simp [Set.mem_Icc]
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide