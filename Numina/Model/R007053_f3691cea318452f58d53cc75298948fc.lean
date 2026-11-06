import Mathlib

theorem algebra_19086 : {x : ℝ | 2 * x + 2 ≠ 0 ∧ x - 1 ≠ 0 ∧ (2 * x - 1) / (2 * x + 2) = (x - 3) / (x - 1)} = {-7} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the set
    rintro ⟨h1, h2, h_eq⟩
    have h1' : 2 * x + 2 ≠ 0 := h1
    have h2' : x - 1 ≠ 0 := h2
    have h3 : (2 * x - 1) * (x - 1) = (x - 3) * (2 * x + 2) := by
      field_simp [h1', h2'] at h_eq ⊢
      linarith
    have h4 : (2 * x - 1) * (x - 1) = 2 * x ^ 2 - 3 * x + 1 := by ring
    have h5 : (x - 3) * (2 * x + 2) = 2 * x ^ 2 - 4 * x - 6 := by ring
    rw [h4] at h3
    rw [h5] at h3
    have h6 : -3 * x + 1 = -4 * x - 6 := by
      nlinarith
    have h7 : x = -7 := by
      linarith
    assumption
  · -- Assume x = -7, prove it is in the set
    intro h
    rw [h]
    constructor
    · -- Show 2x + 2 ≠ 0
      norm_num
    constructor
    · -- Show x - 1 ≠ 0
      norm_num
    · -- Verify the equality
      norm_num