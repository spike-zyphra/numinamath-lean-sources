import Mathlib

theorem algebra_291043 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x = 1 + 1 / y) (h2 : y = 1 + 1 / x) : y = x := by
  have eq1 : x * y = y + 1 := by
    have h1' : x = 1 + 1 / y := h1
    have hy' : y ≠ 0 := hy
    field_simp [hy'] at h1' ⊢
    nlinarith
  
  have eq2 : x * y = x + 1 := by 
    have h2' : y = 1 + 1 / x := h2
    have hx' : x ≠ 0 := hx
    field_simp [hx'] at h2' ⊢
    nlinarith
  
  nlinarith [eq1, eq2]