import Mathlib

theorem number_theory_284702 : {n : ℕ | Even n ∧ n ∈ Finset.Ioo (3^2) (3^3)}.encard = 9 := by
  have h1 : {n : ℕ | Even n ∧ n ∈ Finset.Ioo (3^2) (3^3)} = {10, 12, 14, 16, 18, 20, 22, 24, 26} := by
    ext n
    simp [Finset.mem_Ioo, Nat.even_iff]
    omega
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> rfl