import Mathlib

theorem inequalities_110706 (x : ℝ) (hx : x > 0) : x + 1 / x ≥ 2 := by
  have h1 : x + 1 / x - 2 ≥ 0 := by
    have h2 : x + 1 / x - 2 = (x - 1)^2 / x := by
      field_simp
      ring
    rw [h2]
    have hx1 : x > 0 := hx
    have hx2 : (x - 1)^2 ≥ 0 := by
      apply sq_nonneg
    apply div_nonneg
    linarith
    linarith
  linarith