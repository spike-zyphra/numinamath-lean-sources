import Mathlib

open Real Set

theorem algebra_16437 (x : ℝ) (hx : 0 < x) :
    4 * x ^ 5 + 5 / x ^ 4 ≥ 9 := by
  have h1 : x ^ 4 > 0 := by
    positivity
  have h2 : 4 * x ^ 5 + 5 / x ^ 4 - 9 ≥ 0 := by
    have h3 : 4 * x ^ 9 + 5 - 9 * x ^ 4 ≥ 0 := by
      nlinarith [sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 2 * (x ^ 2 - 1)), sq_nonneg (x ^ 2 * (x ^ 2 + 1)), sq_nonneg (x * (x ^ 2 - 1)), sq_nonneg (x * (x ^ 2 + 1)), sq_nonneg (x * (x - 1)), sq_nonneg (x - 1), mul_pos hx hx, mul_pos hx (show 0 < x by linarith)]
    have h5 : (4 * x ^ 5 + 5 / x ^ 4 - 9) = (4 * x ^ 9 + 5 - 9 * x ^ 4) / x ^ 4 := by
      field_simp
      <;> ring
    rw [h5]
    apply div_nonneg
    linarith [h3]
    positivity
  linarith [h2]