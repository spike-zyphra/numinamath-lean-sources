import Mathlib

theorem algebra_11236 : {x : ℝ | 2 * x ^ 2 + 8 * x ≤ -6} = Set.Icc (-3) (-1) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Assume that 2 * x ^ 2 + 8 * x ≤ -6, prove (-3 ≤ x ∧ x ≤ -1)
    intro h
    constructor
    · -- Prove -3 ≤ x
      nlinarith [sq_nonneg (x + 2)]
    · -- Prove x ≤ -1
      nlinarith [sq_nonneg (x + 2)]
  · -- Assume (-3 ≤ x ∧ x ≤ -1), prove 2 * x ^ 2 + 8 * x ≤ -6
    rintro ⟨h1, h2⟩
    nlinarith [sq_nonneg (x + 2)]