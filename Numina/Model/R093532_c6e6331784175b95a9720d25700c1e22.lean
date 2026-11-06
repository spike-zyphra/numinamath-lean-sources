import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_248302 (a : ℝ) (ha : 5 ≤ a ∧ a ≤ 10) :
    sqrt (a + 3 - 4 * sqrt (a - 1)) + sqrt (a + 8 - 6 * sqrt (a - 1)) = 1 := by
  have h1 : 5 ≤ a := ha.1
  have h2 : a ≤ 10 := ha.2
  have h3 : 4 ≤ a - 1 := by linarith
  have h4 : a - 1 ≤ 9 := by linarith
  have h5 : 2 ≤ sqrt (a - 1) := by
    have h6 : sqrt 4 ≤ sqrt (a - 1) := Real.sqrt_le_sqrt (by linarith)
    have h7 : sqrt 4 = 2 := Real.sqrt_eq_cases.2 (by norm_num)
    linarith
  have h8 : sqrt (a - 1) ≤ 3 := by
    have h9 : sqrt (a - 1) ≤ sqrt 9 := Real.sqrt_le_sqrt (by linarith)
    have h10 : sqrt 9 = 3 := Real.sqrt_eq_cases.2 (by norm_num)
    linarith

  have h11 : a + 3 - 4 * sqrt (a - 1) = (sqrt (a - 1) - 2) ^ 2 := by
    calc
      a + 3 - 4 * sqrt (a - 1) = (a - 1) + 4 - 4 * sqrt (a - 1) := by ring
      _ = (sqrt (a - 1)) ^ 2 + 4 - 4 * sqrt (a - 1) := by rw [Real.sq_sqrt (by linarith)]
      _ = (sqrt (a - 1) - 2) ^ 2 := by ring

  have h12 : a + 8 - 6 * sqrt (a - 1) = (sqrt (a - 1) - 3) ^ 2 := by
    calc
      a + 8 - 6 * sqrt (a - 1) = (a - 1) + 9 - 6 * sqrt (a - 1) := by ring
      _ = (sqrt (a - 1)) ^ 2 + 9 - 6 * sqrt (a - 1) := by rw [Real.sq_sqrt (by linarith)]
      _ = (sqrt (a - 1) - 3) ^ 2 := by ring

  have h13 : sqrt (a + 3 - 4 * sqrt (a - 1)) = abs (sqrt (a - 1) - 2) := by
    rw [h11]
    rw [Real.sqrt_sq_eq_abs]

  have h15 : sqrt (a + 8 - 6 * sqrt (a - 1)) = abs (sqrt (a - 1) - 3) := by
    rw [h12]
    rw [Real.sqrt_sq_eq_abs]

  have h17 : abs (sqrt (a - 1) - 2) = sqrt (a - 1) - 2 := by
    rw [abs_of_nonneg]
    linarith [h5]

  have h18 : abs (sqrt (a - 1) - 3) = 3 - sqrt (a - 1) := by
    have h19 : sqrt (a - 1) - 3 ≤ 0 := by linarith [h8]
    rw [abs_of_nonpos h19]
    ring

  rw [h13, h15, h17, h18]
  linarith