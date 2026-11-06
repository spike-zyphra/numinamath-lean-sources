import Mathlib

theorem algebra_9430 {a : ℝ} (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 3 + x ^ 2)
  (h' : IsLocalExtr f (-4 / 3) ) : a = 1 / 2 := by
  have hderiv : deriv f (-4 / 3) = 0 := by 
    apply h'.deriv_eq_zero
  have eq1 : deriv f (-4 / 3) = a * (16 / 3) - 8 / 3 := by 
    have eq2 : deriv f (-4 / 3) = 3 * a * (-4 / 3) ^ 2 + 2 * (-4 / 3) := by 
      rw [hf]
      simp [deriv_add, deriv_pow, deriv_const_mul, deriv_id'', mul_comm a, mul_assoc]
      <;> field_simp
      all_goals ring
    rw [eq2]
    <;> norm_num
    all_goals ring
  rw [eq1] at hderiv 
  linarith