import Mathlib

theorem inequalities_103408 (x : ℝ) (hx : x > 0) : x + 1 / x ≥ 2 := by
  have h1 : x * (1 / x) = 1 := by
    field_simp [hx]
  have h2 : x + 1 / x - 2 ≥ 0 := by
    have h3 : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := by
      field_simp [hx]
      ring
    rw [h3]
    have h4 : x ^ 2 + 1 - 2 * x ≥ 0 := by
      nlinarith [sq_nonneg (x - 1)]
    apply div_nonneg
    linarith [h4]
    all_goals linarith [show 0 < x by linarith [hx]]
  linarith [h2]