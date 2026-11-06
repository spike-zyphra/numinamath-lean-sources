import Mathlib

theorem algebra_18648 : {x : ℝ | x^2 - 5 * x - 4 ≤ 10} = Set.Icc (-2) 7 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Assume x^2 - 5 * x - 4 ≤ 10, prove -2 ≤ x ∧ x ≤ 7
    intro h
    constructor
    · -- Prove -2 ≤ x
      nlinarith
    · -- Prove x ≤ 7
      nlinarith
  · -- Assume -2 ≤ x ∧ x ≤ 7, prove x^2 - 5 * x - 4 ≤ 10
    rintro ⟨h1, h2⟩
    nlinarith