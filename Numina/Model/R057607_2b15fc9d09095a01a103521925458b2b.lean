import Mathlib

theorem inequalities_108214 (x : ℝ) (hx : x > 0) : x + 1 / x ≥ 2 := by
  have h1 : x + 1 / x - 2 ≥ 0 := by
    have h2 : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := by
      field_simp
      <;> ring
    have h3 : x ^ 2 + 1 - 2 * x ≥ 0 := by
      nlinarith [sq_nonneg (x - 1)]
    have h4 : (x ^ 2 + 1 - 2 * x) / x ≥ 0 := by
      apply div_nonneg
      · linarith [h3]
      · linarith [show x > 0 from hx]
    linarith [h2, h4]
  linarith [h1]