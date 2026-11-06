import Mathlib

theorem algebra_299431 {x y : ℝ} (h1 : x + y = 1) (h2 : x ^ 3 + y ^ 3 = 1 / 3) :
    x ^ 5 + y ^ 5 = 11 / 81 := by
  have eq1 : x * y = 2 / 9 := by
    have h3 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x + y) * (x * y) := by
      ring
    rw [h1] at h3
    linarith

  have eq2 : x ^ 5 + y ^ 5 = (x + y) * (x ^ 4 + y ^ 4) - (x * y) * (x ^ 3 + y ^ 3) := by
    ring

  have eq3 : x ^ 4 + y ^ 4 = (x ^ 2 + y ^ 2) ^ 2 - 2 * ((x * y) ^ 2) := by
    ring

  have eq4 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    ring

  have eq5 : x ^ 2 + y ^ 2 = 5 / 9 := by
    rw [h1, eq1] at eq4
    linarith

  have eq6 : x ^ 4 + y ^ 4 = 17 / 81 := by
    rw [eq5, eq1] at eq3
    linarith

  rw [eq2, h1, h2, eq1, eq6]
  norm_num

  all_goals
    ring_nf
    <;> nlinarith