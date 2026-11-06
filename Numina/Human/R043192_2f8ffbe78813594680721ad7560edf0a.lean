import Mathlib
open Real

/- ## Problem Statement

Find the derivative.


$$

y=\ln \frac{1+\sqrt{-3+4 x-x^{2}}}{2-x}+\frac{2}{2-x} \sqrt{-3+4 x-x^{2}}

$$
 -/
theorem calculus_150847 (x : ℝ) (h : 2 - x ≠ 0) (h' : -3 + 4 * x - x^2 > 0) :
  deriv (fun x ↦ log ((1 + √(-3 + 4 * x - x ^ 2)) / (2 - x)) + (2 / (2 - x)) * √(-3 + 4 * x - x ^ 2)) x
  = (4 - x) / ((2 - x)^2 * √(-3 + 4 * x - x^2)) := by
  -- start with some differentiability facts
  have diff_quad : DifferentiableAt ℝ (fun x ↦ -3 + 4 * x - x^2) x
  · simp
    apply DifferentiableAt.const_mul
    simp
  have diff_sqrt : DifferentiableAt ℝ (fun x ↦ √(-3 + 4 * x - x^2)) x
  · apply DifferentiableAt.sqrt
    exact diff_quad
    exact (ne_of_lt h').symm
  have diff_div : DifferentiableAt ℝ (fun x ↦ 2 / (2 - x)) x
  · apply DifferentiableAt.div
    simp
    apply DifferentiableAt.const_sub
    simp
    exact h
  have sqrt_neq : √(-3 + 4 * x - x^2) ≠ 0 := by exact sqrt_ne_zero'.mpr h'
  have sqrt_neq_add : 1 + √(-3 + 4 * x - x ^ 2) ≠ 0
  · apply ne_of_gt
    calc
      0 < √(-3 + 4 * x - x^2) := sqrt_pos_of_pos h'
      _ < 1 + √(-3 + 4 * x - x^2) := by linarith
  -- expand derivative using product and quotient rules
  rw [deriv_add, deriv.log, deriv_mul _ diff_sqrt, deriv_sqrt diff_quad, deriv_div, deriv_const_sub, deriv_const_add, deriv_sqrt diff_quad, deriv_div, deriv_const_sub, deriv_sub, deriv_const_add, deriv_const_mul]
  simp
  rw [div_div]

  -- simplify result
  calc
    _ = ((2 - x)^2 / (√(-3 + 4 * x - x^2)) + (√(-3 + 4 * x - x^2) + 1)) /
      ((2 - x) * (2 - x) / (2 - x) * ((1 + √(-3 + 4 * x - x^2)))) +
    (2 / (2 - x)^2 * √(-3 + 4 * x - x^2) + 2 * ((2 - x) / (2 - x)) * (1 / (√(-3 + 4 * x - x ^ 2))))
    := by ring
    _ = ((2 - x)^2 / (√(-3 + 4 * x - x^2)) + (√(-3 + 4 * x - x^2) + 1)) /
      ((2 - x) * (1 + √(-3 + 4 * x - x^2)))
      + (2 / (2 - x)^2 * √(-3 + 4 * x - x^2) + 2 * 1 / √(-3 + 4 * x - x ^ 2))
    := by congr; exact mul_div_cancel_right₀ _ h; exact (div_eq_one_iff_eq h).mpr rfl; simp
    _ = ((2 - x)^2 / √(-3 + 4 * x - x^2) + (√(-3 + 4 * x - x^2) / √(-3 + 4 * x - x^2)) * (√(-3 + 4 * x - x^2) + 1)) / ((2 - x) * (1 + √(-3 + 4 * x - x^2)))
    + (2 / (2 - x)^2 * √(-3 + 4 * x - x^2) + 2 * 1 / √(-3 + 4 * x - x ^ 2))
    := by congr; rw [(div_eq_one_iff_eq sqrt_neq).mpr rfl]; ring
    _ = ((2 - x)^2 + (1 + √(-3 + 4 * x - x^2)) * √(-3 + 4 * x - x^2)) / ((2 - x) * √(-3 + 4 * x - x^2) * (1 + √(-3 + 4 * x - x^2))) + (2 / (2 - x)^2 * √(-3 + 4 * x - x^2) + 2 * 1 / (√(-3 + 4 * x - x ^ 2)))
    := by congr 1; field_simp; ring
    _ = (1 + √(-3 + 4 * x - x^2)) / ((2 - x) * √(-3 + 4 * x - x^2) * (1 + √(-3 + 4 * x - x^2)))
    + (2 / (2 - x)^2 * √(-3 + 4 * x - x^2) + 2 * 1 / (√(-3 + 4 * x - x ^ 2)))
    := by congr 2; rw [add_mul, mul_self_sqrt (le_of_lt h')]; ring
    _ = (2 - x) / ((2 - x)^2 * √(-3 + 4 * x - x^2))
    + (2 / (2 - x)^2 * √(-3 + 4 * x - x^2) + 2 * 1 / (√(-3 + 4 * x - x ^ 2)))
    := by congr 1; field_simp; ring
    _ = (2 - x) / ((2 - x)^2 * √(-3 + 4 * x - x^2))
    + (2 * (-3 + 4 * x - x^2) + 2 * (2 - x)^2) / ((2 - x)^2 * √(-3 + 4 * x - x^2))
    := by congr; field_simp; rw [mul_assoc, mul_self_sqrt (le_of_lt h')]
    _ = (4 - x) / ((2 - x) ^ 2 * √(-3 + 4 * x - x ^ 2))
    := by field_simp; ring

  -- Verify everything is differentiable
  · simp
  · simp
    apply DifferentiableAt.const_mul
    simp
  · simp
  · exact differentiableAt_const 2
  · apply DifferentiableAt.const_sub
    simp
  · exact h
  · exact (ne_of_lt h').symm
  · simp
    exact diff_sqrt
  · apply DifferentiableAt.const_sub
    simp
  · exact h
  · exact (ne_of_lt h').symm
  · exact diff_div
  · apply DifferentiableAt.div
    simp
    exact diff_sqrt
    apply DifferentiableAt.const_sub
    simp
    exact h
  · exact div_ne_zero sqrt_neq_add h
  · apply DifferentiableAt.log
    apply DifferentiableAt.div
    simp
    exact diff_sqrt
    apply DifferentiableAt.const_sub
    simp
    exact h
    exact div_ne_zero sqrt_neq_add h
  · exact DifferentiableAt.mul diff_div diff_sqrt