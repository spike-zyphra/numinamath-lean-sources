import Mathlib

theorem algebra_215272 {x Z : ℝ} (hx : x ≠ 0) (hZ : Z = x - 1/x) :
    x^5 - 1/x^5 = Z^5 + 5*Z^3 + 5*Z := by
  rw [hZ]
  field_simp [hx]
  ring