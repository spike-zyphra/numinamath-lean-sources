import Mathlib

theorem algebra_95481 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x = 1 + 1 / y ∧ y = 1 + 1 / x) :
    y = x := by 
  rcases hxy with ⟨hx_eq, hy_eq⟩
  have eq1 : x * y = y + 1 := by 
    field_simp [hy] at hx_eq
    linarith
  have eq2 : x * y = x + 1 := by 
    field_simp [hx] at hy_eq
    linarith
  linarith