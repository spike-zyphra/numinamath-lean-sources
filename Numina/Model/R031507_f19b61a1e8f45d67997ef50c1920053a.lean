import Mathlib

theorem algebra_170160 :
    ∃ a b : ℤ, (∀ x : ℝ, x^2 + a * x + b ≠ 0) ∧
    (∃ x : ℝ, ⌊x^2⌋ + a * x + b = 0) := by
  use 3, 3
  constructor
  · -- Show that x^2 + 3x + 3 ≠ 0 for all x : ℝ
    intro x
    have h : x ^ 2 + (3 : ℝ) * x + (3 : ℝ) ≠ 0 := by
      have h1 : x ^ 2 + (3 : ℝ) * x + (3 : ℝ) > 0 := by
        nlinarith [sq_nonneg (x + (3 : ℝ) / 2)]
      linarith
    simpa using h
  · -- Show that ∃ x : ℝ, ⌊x^2⌋ + 3 * x + 3 = 0
    use (-4 / 3 : ℝ)
    norm_num
    <;> try { norm_num }
    <;> try { linarith }