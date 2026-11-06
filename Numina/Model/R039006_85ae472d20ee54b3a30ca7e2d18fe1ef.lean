import Mathlib

theorem algebra_14676 : {y : ℝ | y - 1 ≠ 0 ∧ 3 * y - 2 ≠ 0 ∧ (y ^ 2 - 9 * y + 8) / (y - 1) + (3 * y ^ 2 + 16 * y - 12) / (3 * y - 2) = -3} = {-1/2} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, prove the forward direction: if y is in the set, then y = -1/2
    intro h
    rcases h with ⟨h1, h2, heq⟩
    have eq1 : (y ^ 2 - 9 * y + 8) / (y - 1) = y - 8 := by
      have h1' : y - 1 ≠ 0 := h1
      field_simp [h1']
      ring
    have eq2 : (3 * y ^ 2 + 16 * y - 12) / (3 * y - 2) = y + 6 := by
      have h2' : 3 * y - 2 ≠ 0 := h2
      field_simp [h2']
      ring
    rw [eq1, eq2] at heq
    linarith
  · -- Now, prove the reverse direction: if y = -1/2, then y is in the set
    intro h
    rw [h]
    constructor
    · -- Show y - 1 ≠ 0
      norm_num
    constructor
    · -- Show 3 * y - 2 ≠ 0
      norm_num
    · -- Verify the equation
      norm_num