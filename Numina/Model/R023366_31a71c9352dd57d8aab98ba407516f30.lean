import Mathlib

theorem inequalities_602392 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 2) :
    x ^ 3 * y ^ 3 * (x ^ 3 + y ^ 3) ≤ 2 := by
  have h1 : y = 2 - x := by linarith
  have h2 : 0 < y := by nlinarith [hxy, hx]
  have h3 : x * y ≤ 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), hxy]
  have h4 : x ^ 3 + y ^ 3 = 8 - 6 * (x * y) := by
    have h5 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
      ring
    rw [h5, hxy]
    all_goals norm_num
    all_goals nlinarith
  have h6 : x ^ 3 * y ^ 3 * (x ^ 3 + y ^ 3) = (x * y) ^ 3 * (8 - 6 * (x * y)) := by
    rw [h4]
    ring_nf
  rw [h6]
  nlinarith [sq_nonneg ((x * y) ^ 2 - 1), sq_nonneg ((x * y) - 1),
    sq_nonneg ((x * y) * (x * y - 1)), sq_nonneg (x * y - 1),
    mul_pos hx (by nlinarith [h1, hx] : 0 < y), h3, sq_nonneg ((x * y) ^ 2 - (x * y)), sq_nonneg (x * y - 1)]