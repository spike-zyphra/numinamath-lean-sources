import Mathlib

theorem algebra_318633 {a b c d α : ℝ} (ha : a ≠ c) (h1 : α^2 + a * α + b = 0) (h2 : α^2 + c * α + d = 0) :
    α = (d - b) / (a - c) := by

  have eq1 : (a - c) * α = d - b := by
    linarith
  have h3 : a - c ≠ 0 := by
    intro h
    apply ha
    linarith
  have eq2 : α = (d - b) / (a - c) := by
    field_simp [h3]
    linarith
  exact eq2