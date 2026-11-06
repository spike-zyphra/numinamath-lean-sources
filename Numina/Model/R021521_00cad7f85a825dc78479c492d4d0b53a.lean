import Mathlib

theorem algebra_11757 : (3 / 8 : ℝ) = {x | x ∈ Finset.range 8 ∧ (x = 1 ∨ x = 3 ∨ x = 6)}.ncard / 8 := by
  have h1 : {x | x ∈ Finset.range 8 ∧ (x = 1 ∨ x = 3 ∨ x = 6)} = {1, 3, 6} := by
    ext n
    simp [Finset.mem_range]
    <;> omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> norm_num