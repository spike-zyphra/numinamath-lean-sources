import Mathlib

theorem inequalities_120653 (x : ℝ) (hx : x > 0) : x + 1 / x ≥ 2 := by
  have h1 : x + 1 / x - 2 ≥ 0 := by
    have h2 : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := by
      field_simp
      <;> ring
    rw [h2] at *
    have h3 : x ^ 2 + 1 - 2 * x ≥ 0 := by
      nlinarith [sq_nonneg (x - 1)]
    have h4 : x > 0 := hx
    apply div_nonneg 
    linarith 
    linarith 
  linarith