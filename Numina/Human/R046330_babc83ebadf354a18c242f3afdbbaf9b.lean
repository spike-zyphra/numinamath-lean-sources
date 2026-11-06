import Mathlib

/- 1. [3] Suppose that $x$ and $y$ are positive reals such that\n$$\nx-y^{2}=3, \\quad x^{2}+y^{4}=13 .\n$$\n\nFind $x$. -/
theorem algebra_156771 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x - y^2 = 3) (h2 : x^2 + y^4 = 13) :
    x = (3 + √17) / 2 := by
  have h3 : x = y^2 + 3 := by linarith
  rw [h3] at h2
  have hy2 : y^2 = (-3 + √17) / 2 := by
    have h_factored : (y^2 - (-3 + √17) / 2) * (y^2 - (-3 - √17) / 2) = 0 := by
      ring_nf
      simp
      linarith only [h2]
    rcases (mul_eq_zero.mp h_factored) with h | h
    · linarith only [h]
    · exfalso
      have h_sqrt_pos : 0 < √17 := by positivity
      have h_y2_nonneg : 0 ≤ y^2 := sq_nonneg y
      linarith only [h_sqrt_pos, h_y2_nonneg, h]
  rw [hy2] at h3
  linarith
