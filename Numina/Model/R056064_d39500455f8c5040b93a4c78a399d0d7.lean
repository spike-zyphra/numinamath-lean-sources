import Mathlib

theorem algebra_305396 (s : ℝ) :
    (∀ t : ℝ, ∃ x : ℝ, s * x ^ 2 + t * x + s - 1 = 0) ↔
    0 < s ∧ s ≤ 1 := by
  constructor
  · -- Forward implication: if the equation has real roots for any real t, then 0 < s ≤ 1
    intro h
    have h1 := h 0
    rcases h1 with ⟨x1, hx1⟩
    have h2 : s > 0 := by
      nlinarith [sq_nonneg x1, sq_nonneg (x1 ^ 2)]
    have h3 : s ≤ 1 := by
      nlinarith [sq_nonneg x1, sq_nonneg (s * x1 ^ 2), sq_nonneg (x1 ^ 2)]
    constructor
    · exact h2
    · exact h3
  · -- Backward implication: if 0 < s ≤ 1, then the equation has real roots for any real t
    rintro ⟨h1, h2⟩
    intro t
    have h3 : ∃ x : ℝ, s * x^2 + t * x + s - 1 = 0 := by
      have hdisc : t ^ 2 - 4 * s * (s - 1) ≥ 0 := by
        nlinarith [sq_nonneg (t), sq_nonneg (s - 1)]
      use (-t + Real.sqrt (t ^ 2 - 4 * s * (s - 1))) / (2 * s)
      field_simp
      nlinarith [Real.sqrt_nonneg (t^2 - 4 * s * (s - 1)), Real.sq_sqrt (show t^2 - 4 * s * (s - 1) ≥ 0 by linarith [hdisc])]
    exact h3