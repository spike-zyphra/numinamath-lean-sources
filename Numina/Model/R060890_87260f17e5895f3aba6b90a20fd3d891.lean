import Mathlib

theorem algebra_107932 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (1 + x / 100) * (1 - y / 100) = 1) :
    1 / x - 1 / y = -1 / 100 := by 
  have h1 : (1 + x / 100) * (1 - y / 100) = 1 := h
  -- expand the constraint
  -- (1 + x/100)(1 - y/100) = 1
  -- (1 + x/100)(1 - y/100) = 1 + x/100 - y/100 - (x*y)/10000 = 1
  -- so x/100 - y/100 - (x * y)/10000 = 0
  have formula1 : x / 100 - y / 100 - x * y / 10000 = 0 := by
    linarith [h1]
  have formula2 : (x - y) / 100 - x * y / 10000 = 0 := by 
    linarith [formula1]
  -- from h, we now have $(x - y)/100 - (x*y)/10000 = 0$
  have h2 : 1 / x - 1 / y = (y - x) / (x * y) := by
    field_simp [hx, hy]
    <;> ring
  have h3 : x * y = 100 * (x - y) := by
    field_simp at formula2 ⊢ 
    linarith [formula2]
  have h4 : (y - x) = - (x * y) / 100 := by 
    have h5 : x * y = 100 * (x - y) := by linarith [h3]
    linarith [h5]
  rw [h2]
  rw [h4]
  have h_nonzero : x * y ≠ 0 := by 
    apply mul_ne_zero 
    exact hx
    exact hy
  have eq1 : (- (x * y) / 100) / (x * y) = -1 / 100 := by 
    field_simp [h_nonzero]
    <;> linarith
  linarith [eq1]