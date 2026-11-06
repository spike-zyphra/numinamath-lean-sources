import Mathlib

theorem inequalities_133247 (x : ℝ) (hx : x ≠ 0) :
    x ^ 8 - x ^ 5 - 1 / x + 1 / x ^ 4 ≥ 0 := by
  have h2 : (x ^ 4) > 0 := by
    positivity
  have h3 : x ^ 8 - x ^ 5 - 1 / x + 1 / x ^ 4 ≥ 0 ↔ (x ^ 8 - x ^ 5 - 1 / x + 1 / x ^ 4) * (x ^ 4) ≥ 0 := by
    apply Iff.intro
    · -- Forward implication: if original expression is ≥ 0 then multiplying by positive is ≥ 0.
      intro h
      nlinarith
    · -- Backward implication: if multiplying by positive is ≥ 0, then original is ≥ 0.
      intro h
      nlinarith
  rw [h3]
  have h4 : (x ^ 8 - x ^ 5 - 1 / x + 1 / x ^ 4) * (x ^ 4) = x ^ 12 - x ^ 9 - x ^ 3 + 1 := by
    field_simp [hx]
    <;> ring
  rw [h4]
  nlinarith [sq_nonneg (x ^ 3 - 1), sq_nonneg (x ^ 6 - 1), sq_nonneg (x ^ 3 - x), sq_nonneg (x ^ 3 + 1), sq_nonneg (x ^ 6 + x ^ 3 + 1), sq_nonneg (x ^ 6 - x ^ 3)]