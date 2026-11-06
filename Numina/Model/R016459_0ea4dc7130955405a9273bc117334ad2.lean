import Mathlib

theorem calculus_22187 (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (h1 : 3 + 2 * t = -5 + 4 * u) (h2 : -10 - 9 * t = -3 - 18 * u)
    (h3 : 1 - 2 * t = 6 - 4 * u) :
    Real.sqrt ((2 - 4)^2 + (-9 - 18)^2 + (-2 - 4)^2) = 7 := by
  have eq1 : t - 2 * u = -4 := by
    nlinarith
  have eq2 : t - 2 * u = -5 / 2 := by
    linarith
  have h : ( -4 : ℝ ) = -5 / 2 := by
    linarith [eq1, eq2]
  norm_num at h