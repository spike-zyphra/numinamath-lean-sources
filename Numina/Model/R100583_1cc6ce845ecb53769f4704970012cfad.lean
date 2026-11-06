import Mathlib

theorem algebra_96548 {x : ℝ} (hx : x < 0) :
    Real.sqrt (x / (1 - (x - 1) / x)) = -x := by
  have h1 : x ≠ 0 := by linarith
  have h2 : 1 - (x - 1) / x = 1 / x := by
    field_simp [h1]
    <;> ring
  have h3 : x / (1 - (x - 1) / x) = x ^ 2 := by
    rw [h2]
    field_simp [h1]
    <;> ring
  rw [h3]
  have h4 : Real.sqrt (x ^ 2) = abs x := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h4]
  rw [abs_of_neg hx]
  all_goals linarith