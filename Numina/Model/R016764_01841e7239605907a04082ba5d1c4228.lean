import Mathlib

open Real Set

theorem algebra_15399 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 10) :
    1 / x + 1 / y ≥ 2 / 5 := by
  have h1 : 1 / x + 1 / y = (x + y) / (x * y) := by
    field_simp
    <;> ring
  rw [h1, hxy]
  have h2 : x * y ≤ 25 := by
    have h3 : x * y ≤ ((x + y) / 2) ^ 2 := by 
      nlinarith [sq_nonneg (x - y)]
    rw [hxy] at h3
    nlinarith
  have h3 : 10 / (x * y) ≥ 2 / 5 := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (x - y), h2]
  linarith [h3]