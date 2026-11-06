import Mathlib

/- A rectangle has perimeter 10 and diagonal $\sqrt{15}$. What is its area?-/
theorem geometry_611219 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hperi : 2 * x + 2 * y = 10) (hdiag : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt 15) : x * y = 5 := by
  -- First show that x² + y² = 15.
  rw [<-sq_eq_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)] at hdiag
  -- Also note that x² + 2xy + y² = 25.
  rw [<-sq_eq_sq₀ (by positivity) (by positivity)] at hperi
  -- Now solve to get xy = 5.
  linarith
