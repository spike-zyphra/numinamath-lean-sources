import Mathlib

theorem algebra_187171 {x y : ℝ} (hx : x^2 - 2000 * x = y^2 - 2000 * y) (hy : x ≠ y) :
    x + y = 2000 := by
  have h1 : x^2 - 2000 * x - (y^2 - 2000 * y) = 0 := by linarith
  have h2 : x^2 - y^2 - 2000 * (x - y) = 0 := by 
    linarith [h1]
  have h3 : (x - y) * (x + y - 2000) = 0 := by
    ring_nf at h2 ⊢
    linarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case where $x - y = 0$, which implies $x = y$, contradicting $x \neq y$.
    exfalso
    exact hy (eq_of_sub_eq_zero h4)
  · -- Case where $x + y - 2000 = 0$, which implies $x + y = 2000$.
    linarith