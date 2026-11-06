import Mathlib

theorem algebra_4785 : {x : ℝ | 0 ≤ x ∧ x ≤ 100 ∧ (10 * 12 / 100 + 14 * x / 100) / (10 + 14) ∈ Set.Icc (8.5 / 100) (19 / 100)} = {x : ℝ | 6 ≤ x ∧ x ≤ 24} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Forward direction: If x satisfies all constraints, then 6 ≤ x ≤ 24
    rintro ⟨hx₁, hx₂, ⟨hx₃, hx₄⟩⟩
    norm_num at hx₃ hx₄
    constructor
    · -- Solving the lower bound inequality
      linarith
    · -- Solving the upper bound inequality
      linarith
  · -- Backward direction: If 6 ≤ x ≤ 24, then x satisfies all constraints
    rintro ⟨hx₁, hx₂⟩
    constructor
    · -- Show 0 ≤ x
      linarith
    constructor
    · -- Show x ≤ 100
      linarith
    · -- Show the concentration constraints
      constructor
      · -- Show lower bound
        norm_num
        linarith
      · -- Show upper bound
        norm_num
        linarith