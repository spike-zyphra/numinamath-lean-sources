import Mathlib

theorem algebra_145469 (x y : ℝ) : 6*x^2+10*x+25+5*y^2+10*x*y=0 ↔ (x=-5 ∧ y=5) := by
  constructor
  · -- (→) Assume 6*x^2+10*x+25+5*y^2+10*x*y=0, prove (x=-5 ∧ y=5)
    intro h
    have h1 : 5 * (y + x) ^ 2 + (x + 5) ^ 2 = 0 := by
      nlinarith
    have h2 : 5 * (y + x) ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (y + x)]
    have h3 : (x + 5) ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (x + 5)]
    have h4 : 5 * (y + x) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y + x), sq_nonneg (x + 5)]
    have h5 : (x + 5) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y + x), sq_nonneg (x + 5)]
    have h6 : y + x = 0 := by
      nlinarith [sq_nonneg (y + x)]
    have h7 : x + 5 = 0 := by
      nlinarith [sq_nonneg (x + 5)]
    constructor
    · -- prove x = -5
      linarith
    · -- prove y = 5
      nlinarith [h6, h7]
  · -- (←) Assume (x=-5 ∧ y=5), prove 6*x^2+10*x+25+5*y^2+10*x*y=0
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num