import Mathlib

theorem algebra_199308 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 6 + 8) (h : (6 - x) * (8 - y) = x * y) :
    x = 2.4 ∧ y = 3.6 := by
  have h1 : x + y = 14 := by linarith
  have h2 : (x - 2.4) * (y - 3.6) = 0 := by
    ring_nf
    nlinarith
  cases' (mul_eq_zero.mp h2) with hx' hy'
  · -- Case where x = 2.4
    have hx_eq : x = 2.4 := by linarith
    have hy_eq : y = 3.6 := by linarith [h1, hx_eq]
    exact ⟨hx_eq, hy_eq⟩
  · -- Case where y = 3.6
    have hy_eq : y = 3.6 := by linarith
    have hx_eq : x = 2.4 := by linarith [h1, hy_eq]
    exact ⟨hx_eq, hy_eq⟩