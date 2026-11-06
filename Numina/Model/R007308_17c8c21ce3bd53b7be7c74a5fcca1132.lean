import Mathlib

theorem algebra_10609 : {r : ℝ | r - 3 ≠ 0 ∧ r + 5 ≠ 0 ∧ (r + 9) / (r - 3) = (r - 2) / (r + 5)} = {-39 / 19} := by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume r satisfies all conditions, prove r = -39/19
    rintro ⟨h1, h2, heq⟩
    field_simp [h1, h2] at heq
    linarith
  · -- Assume r = -39/19, prove it satisfies all conditions
    intro heqr
    rw [heqr]
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num