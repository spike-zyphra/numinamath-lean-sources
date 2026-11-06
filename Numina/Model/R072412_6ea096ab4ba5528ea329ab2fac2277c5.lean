import Mathlib

theorem algebra_273713 (m : ℝ) (h : m ≠ 0) (x1 x2 x3 : ℝ)
    (hx1 : x1 = -2 / m) (hx2 : x2 = -3 / m) (hx3 : x3 = -4 / m)
    (hsum : x1 + x2 + x3 = 36) :
    m = -1 / 4 := by
  -- Substitute expressions for x1, x2, x3 into sum
  have eq1 : x1 + x2 + x3 = (-2 / m) + (-3 / m) + (-4 / m) := by 
    rw [hx1, hx2, hx3]
  rw [eq1] at hsum
  -- Simplify the left side
  have eq2 : (-2 / m) + (-3 / m) + (-4 / m) = (-9 / m) := by 
    field_simp [h]
    <;> ring
  rw [eq2] at hsum
  have eq3 : -9 / m = 36 := by 
    linarith 
  have eq4 : m = -1 / 4 := by 
    field_simp [h] at eq3 ⊢
    linarith 
  exact eq4