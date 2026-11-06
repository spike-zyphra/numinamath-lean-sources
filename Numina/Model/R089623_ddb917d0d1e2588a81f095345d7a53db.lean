import Mathlib

theorem algebra_187099 {x y : ℝ} (h1 : x^3 + y^3 = 35) (h2 : x + y = 5) :
    (x, y) = (2, 3) ∨ (x, y) = (3, 2) := by 
  have h3 : y = 5 - x := by linarith
  rw [h3] at h1
  have h4 : x^2 - 5 * x + 6 = 0 := by
    ring_nf at h1
    linarith
  have h5 : (x - 2) * (x - 3) = 0 := by
    linarith [h4]
  cases' (mul_eq_zero.mp h5) with hx2 hx3
  · -- Case $x - 2 = 0$, so $x = 2$
    have hx2' : x = 2 := by linarith
    have hy3' : y = 3 := by linarith [h3, hx2']
    left
    simp [hx2', hy3']
  · -- Case $x - 3 = 0$, so $x = 3$
    have hx3' : x = 3 := by linarith
    have hy2' : y = 2 := by linarith [h3, hx3']
    right
    simp [hx3', hy2']