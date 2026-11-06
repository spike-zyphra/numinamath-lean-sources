import Mathlib

theorem algebra_142338 {x y : ℝ} (hxy : x ≠ y) (h : x^2 - 2000 * x = y^2 - 2000 * y) : x + y = 2000 := by
  have h1 : x^2 - y^2 - 2000 * (x - y) = 0 := by linarith 
  have h2 : (x - y) * (x + y - 2000) = 0 := by 
    ring_nf at h1 ⊢
    linarith
  have h3 : x - y ≠ 0 := sub_ne_zero_of_ne hxy
  have h4 : x + y - 2000 = 0 := by 
    apply (mul_eq_zero.mp h2).resolve_left 
    exact h3
  linarith