import Mathlib

theorem algebra_97912 (m : ℝ) :
    ∃ x y, y = m * x + 3 ∧ y = (2 * m - 1) * x + 4 ↔ m ≠ 1 := by
  by_cases h : m = 1
  · -- Suppose m = 1
    use 0, 0
    simp [h]
  · -- Assume m ≠ 1
    use 1 / (1 - m), m * (1 / (1 - m)) + 3
    constructor
    · -- Assume (y = m * x + 3 ∧ y = (2 * m - 1) * x + 4), prove m ≠ 1
      intro h
      tauto
    · -- Assume m ≠ 1, prove (y = m * x + 3 ∧ y = (2 * m - 1) * x + 4)
      intro h
      constructor
      · -- Show y = m * x + 3
        field_simp [(show (1 - m) ≠ 0 by
          intro h'
          apply h
          linarith
        )]
        <;> ring
      · -- Show y = (2 * m - 1) * x + 4
        field_simp [(show (1 - m) ≠ 0 by
          intro h'
          apply h
          linarith
        )]
        <;> ring