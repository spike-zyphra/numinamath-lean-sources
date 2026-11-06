import Mathlib

def s (t : ℝ) := 3 * t ^ 2 - 2 * t + 4

noncomputable def v (t : ℝ) := deriv s t

theorem calculus_155776 : v 5 = 28 := by
  have hs : s = fun (t : ℝ) => 3 * t^2 - 2 * t + 4 := by
    funext
    all_goals simp [s]

  have h1 : v 5 = deriv s 5 := by
    simp [v]

  rw [h1]
  rw [hs]

  simp [deriv_const, deriv_add, deriv_sub, deriv_pow, deriv_mul, mul_comm]
  all_goals norm_num