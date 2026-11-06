import Mathlib

theorem algebra_255675 :
  { x : ℝ | x > 0 ∧ x * 1 / (4 : ℝ) + x * 1 / 4 + x * 1 / 12 = 1 } = { 12 / 7 } := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- If x satisfies x * 1/4 + x * 1/4 + x * 1/12 = 1 and x > 0, then x = 12/7
    rintro ⟨hx1, hx2⟩
    have h1 : x * (7 / 12 : ℝ) = 1 := by
      linarith
    have h2 : x = (12 / 7 : ℝ) := by
      linarith
    linarith
  · -- If x = 12/7, then x satisfies x * 1/4 + x * 1/4 + x * 1/12 = 1 and x > 0
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num