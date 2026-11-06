import Mathlib

open Real

theorem calculus_126966 (f : ℝ → ℝ) (hf : f = fun x => (3 * x + cos x) ^ ((1 : ℝ) / 3)) (x : ℝ) (hx : x = 0.01) :
    deriv f 0 * (x - 0) + f 0 = 1.01 := by
  have h1 : f = fun x => (3 * x + cos x) ^ ((1 : ℝ) / 3) := by
    exact hf
  have h2 : f 0 = 1 := by
    rw [h1]
    norm_num [cos_zero]
  have h3 : deriv f 0 = 1 := by
    rw [h1]
    simp [deriv_pow, deriv_add, deriv_mul, deriv_id'', mul_comm]
    all_goals norm_num [cos_zero, sin_zero]
    <;> field_simp <;> norm_num [cos_zero, sin_zero]
  rw [h3, h2, hx]
  all_goals norm_num