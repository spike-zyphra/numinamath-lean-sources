import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_107144 {x y : ℝ} :
  3 * x ^ 2 + 4 * sqrt 6 * x + 8 - y ^ 2 =
  (x * sqrt 3 + 2 * sqrt 2 - y) * (x * sqrt 3 + 2 * sqrt 2 + y) := by

  have h1 : sqrt 6 = sqrt 3 * sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num)]
    all_goals norm_num

  have h2 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by linarith [Real.sqrt_nonneg 3])
  have h3 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith [Real.sqrt_nonneg 2])
  have h4 : sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by linarith [Real.sqrt_nonneg 6])

  have h5 : (x * sqrt 3 + 2 * sqrt 2) ^ 2 = 3 * x ^ 2 + 4 * x * sqrt 6 + 8 := by
    calc
      (x * sqrt 3 + 2 * sqrt 2) ^ 2
          = (x * sqrt 3) ^ 2 + 2 * (x * sqrt 3) * (2 * sqrt 2) + (2 * sqrt 2) ^ 2 := by ring
      _ = x^2 * (sqrt 3 ^ 2) + 4 * x * (sqrt 3 * sqrt 2) + 4 * (sqrt 2 ^ 2) := by
          ring
      _ = x^2 * 3 + 4 * x * (sqrt 3 * sqrt 2) + 4 * 2 := by
          rw [h2, h3]
      _ = x^2 * 3 + 4 * x * (sqrt 6) + 4 * 2 := by
          rw [show sqrt 3 * sqrt 2 = sqrt 6 by linarith [h1]]
      _ = 3 * x ^ 2 + 4 * x * sqrt 6 + 8 := by
          ring

  calc
    3 * x ^ 2 + 4 * sqrt 6 * x + 8 - y ^ 2
      = ((x * sqrt 3 + 2 * sqrt 2) ^ 2 - y ^ 2) := by
        have h6 : (x * sqrt 3 + 2 * sqrt 2) ^ 2 - y ^ 2 = (3 * x ^ 2 + 4 * x * sqrt 6 + 8) - y ^ 2 := by
          linarith [h5]
        linarith [h6]
    _ = (x * sqrt 3 + 2 * sqrt 2 - y) * (x * sqrt 3 + 2 * sqrt 2 + y) := by
      have h7 : (x * sqrt 3 + 2 * sqrt 2 - y) * (x * sqrt 3 + 2 * sqrt 2 + y) =
        ((x * sqrt 3 + 2 * sqrt 2) ^ 2 - y ^ 2) := by
        ring
      linarith [h7]