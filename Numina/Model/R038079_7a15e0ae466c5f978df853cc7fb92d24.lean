import Mathlib

theorem algebra_172768 {x y : ℝ} (hx : x + y = 3) (hy : 1 / (x + y ^ 2) + 1 / (x ^ 2 + y) = 1 / 2) :
    x ^ 5 + y ^ 5 = 123 := by

  have h1 : y = 3 - x := by linarith
  have eq1 : x + y ^ 2 = x ^ 2 - 5 * x + 9 := by
    rw [h1]
    nlinarith
  have eq2 : x ^ 2 + y = x ^ 2 - x + 3 := by
    rw [h1]
    nlinarith
  have eq3 : 1 / (x + y ^ 2) + 1 / (x ^ 2 + y) = 1 / (x ^ 2 - 5 * x + 9) + 1 / (x ^ 2 - x + 3) := by
    rw [eq1, eq2]
  rw [eq3] at hy
  have h2 : x ^ 2 - 5 * x + 9 ≠ 0 := by
    by_contra h
    nlinarith [sq_nonneg (x - 5 / 2), sq_nonneg (y + 5 / 2), sq_nonneg (x - y)]
  have h3 : x ^ 2 - x + 3 ≠ 0 := by
    by_contra h
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (x - y)]
  have eq4 : 2 * ((x ^ 2 - 5 * x + 9) + (x ^ 2 - x + 3)) = (x ^ 2 - 5 * x + 9) * (x ^ 2 - x + 3) := by
    field_simp [h2, h3] at hy
    nlinarith [sq_nonneg (x ^ 2 - 5 * x + 9 - (x ^ 2 - x + 3)), sq_nonneg (x ^ 2 - 5 * x + 9 + (x ^ 2 - x + 3)), sq_nonneg (x - 3 / 2)]
  have h31 : x ^ 2 - 3 * x + 1 = 0 := by
    nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (x * (x - 3)), sq_nonneg (x - 3), sq_nonneg ((x ^ 2 - 5 * x + 9) - (x ^ 2 - x + 3))]
  have h41 : x * y = 1 := by
    rw [show y = 3 - x by linarith]
    nlinarith [h31]
  have h01 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    nlinarith
  have h02 : x ^ 2 + y ^ 2 = 7 := by
    rw [h01, hx, h41]
    norm_num
  have h03 : x ^ 3 + y ^ 3 = (x + y) * (x ^ 2 + y ^ 2) - (x * y) * (x + y) := by
    nlinarith [sq_nonneg (x * y)]
  have h04 : x ^ 3 + y ^ 3 = 18 := by
    rw [h03, hx, h02, h41]
    norm_num
  have h05 : x ^ 4 + y ^ 4 = (x + y) * (x ^ 3 + y ^ 3) - (x * y) * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x * y)]
  have h06 : x ^ 4 + y ^ 4 = 47 := by
    rw [h05, hx, h04, h41, h02]
    norm_num
  have h07 : x ^ 5 + y ^ 5 = (x + y) * (x ^ 4 + y ^ 4) - (x * y) * (x ^ 3 + y ^ 3) := by
    nlinarith [sq_nonneg (x * y)]
  rw [h07, hx, h06, h41, h04]
  all_goals norm_num