import Mathlib

theorem algebra_3264 {x y : ℝ} (hnezero : y^2 - 1 ≠ 0)
    (h1 : x - 1 + 2 / (y^2 - 1) = 8 / 3) (h2 : x - 1 / (y^2 - 1) = 8 / 3) :
    x + y^2 = 7 := by 
  have eq3 : (x - 1) * (y^2 - 1) + 2 = (8 / 3) * (y^2 - 1) := by 
    have h' : y^2 - 1 ≠ 0 := hnezero
    have eq3 : x - 1 + 2 / (y^2 - 1) = 8 / 3 := h1
    field_simp [h'] at eq3 ⊢
    nlinarith
    <;> nlinarith
  have eq4 : x * (y^2 - 1) - 1 = (8 / 3) * (y^2 - 1) := by 
    have h' : y^2 - 1 ≠ 0 := hnezero
    have eq4 : x - 1 / (y^2 - 1) = 8 / 3 := h2
    field_simp [h'] at eq4 ⊢
    nlinarith
    <;> nlinarith
  have eq5 : (y^2 - 1) = 3 := by
    nlinarith [eq3, eq4]
  have hy : y^2 = 4 := by
    linarith [eq5]
  have hx : x = 3 := by
    rw [show y^2 - 1 = 3 by linarith [eq5]] at eq4
    nlinarith
  nlinarith [hx, hy]