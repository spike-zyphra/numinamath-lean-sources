import Mathlib

theorem inequalities_189910 (x : ℝ) :
    (5 * x - 20 ≤ x ^ 2 ∧ x ^ 2 ≤ 8 * x) ↔ x ∈ Set.Icc 0 8 := by
  simp only [Set.mem_Icc]
  constructor
  · -- Forward implication: if 5x - 20 ≤ x^2 and x^2 ≤ 8x, then 0 ≤ x ≤ 8
    rintro ⟨h1, h2⟩
    constructor
    · -- Prove x ≥ 0
      nlinarith [sq_nonneg (x - 4)]
    · -- Prove x ≤ 8
      nlinarith [sq_nonneg (x - 4)]
  · -- Backward implication: if 0 ≤ x ≤ 8, then 5x - 20 ≤ x^2 and x^2 ≤ 8x
    rintro ⟨hx1, hx2⟩
    constructor
    · -- Prove 5x - 20 ≤ x^2
      nlinarith [sq_nonneg (x - 5 / 2)]
    · -- Prove x^2 ≤ 8x
      nlinarith [sq_nonneg (x - 4)]