import Mathlib

theorem inequalities_103212 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
    1 / y ^ 2 ≤ 1 / x ^ 2 := by
  have h1 : x ^ 2 ≤ y ^ 2 := by
    nlinarith
  have h2 : 0 < x ^ 2 := by nlinarith
  have h3 : 0 < y ^ 2 := by nlinarith
  apply (div_le_div_iff (by positivity) (by positivity)).mpr
  nlinarith