import Mathlib
open Real

/- ## Problem Statement

Find the derivative.


$$

y=\frac{1}{4} \ln \left|\operatorname{th} \frac{x}{2}\right|-\frac{1}{4} \cdot \ln \frac{3+\operatorname{ch} x}{\operatorname{sh} x}

$$
 -/
theorem calculus_153055 (x : ℝ) (h : x ≠ 0) :
  deriv (fun x ↦ log (tanh (x / 2)) / 4 - log ((3 + cosh x) / sinh x) / 4) x = (1 + cosh x) / (sinh x * (3 + cosh x)) := by
  -- First some inequalities
  have h' : sinh x ≠ 0 := by exact sinh_ne_zero.mpr h
  have h'' : sinh (x / 2) ≠ 0 := by apply sinh_ne_zero.mpr; field_simp; assumption
  have ineq : (3 + cosh x) / sinh x ≠ 0
  · apply div_ne_zero
    apply ne_of_gt
    calc
      0 < cosh x := cosh_pos _
      _ < 3 + cosh x := by linarith
    exact h'
  conv =>
    lhs
    congr
    intro x
    rw [tanh_eq_sinh_div_cosh]
  -- compute the derivative using chain, product, quotient rules
  rw [deriv_sub, deriv_div, deriv.log, deriv_div, deriv_div, deriv.log, deriv_div, Real.deriv_sinh]
  simp only [
    differentiableAt_id', DifferentiableAt.div_const, _root_.deriv_sinh, deriv_div_const, deriv_id'',
    _root_.deriv_cosh, deriv_const', mul_zero, sub_zero, differentiableAt_const, differentiableAt_cosh,
    deriv_add, Real.deriv_cosh, zero_add
  ]
  calc
    _ = 1 / (4 * (2 * sinh (x / 2) * cosh (x / 2))) - (((sinh x)^2 - (cosh x)^2) - 3 * cosh x) / (4 * sinh x * (3 + cosh x))
    := by congr 1; field_simp; rw [←pow_two, ←pow_two, Real.cosh_sq_sub_sinh_sq (x / 2)]; ring; field_simp; ring
    _ = 1 / (4 * sinh x) - (((sinh x)^2 - (cosh x)^2) - 3 * cosh x) / (4 * sinh x * (3 + cosh x))
    := by congr 1; rw [←Real.sinh_two_mul (x / 2)]; congr; ring
    _ = 1 / (4 * sinh x) - (-1 - 3 * cosh x) / (4 * sinh x * (3 + cosh x))
    := by congr; rw [←neg_sub, Real.cosh_sq_sub_sinh_sq]
    _ = (1 + cosh x) / (sinh x * (3 + cosh x))
    := by field_simp; ring

  -- Show everything is differentiable
  · simp only [differentiableAt_const, differentiableAt_cosh, DifferentiableAt.add]
  · simp only [differentiableAt_sinh]
  · exact h'
  · apply DifferentiableAt.div
    simp only [differentiableAt_const, differentiableAt_cosh, DifferentiableAt.add]
    simp only [differentiableAt_sinh]
    exact h'
  · exact ineq
  · apply DifferentiableAt.log
    apply DifferentiableAt.div
    simp only [differentiableAt_const, differentiableAt_cosh, DifferentiableAt.add]
    simp only [differentiableAt_sinh]
    exact h'
    exact ineq
  · simp only [differentiableAt_const]
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  · simp only [differentiableAt_id', DifferentiableAt.div_const, DifferentiableAt.sinh]
  · simp only [differentiableAt_id', DifferentiableAt.div_const, DifferentiableAt.cosh]
  · exact ne_of_gt (cosh_pos _)
  · apply DifferentiableAt.div
    simp only [differentiableAt_id', DifferentiableAt.div_const, DifferentiableAt.sinh]
    simp only [differentiableAt_id', DifferentiableAt.div_const, DifferentiableAt.cosh]
    exact ne_of_gt (cosh_pos _)
  · apply div_ne_zero
    exact h''
    exact ne_of_gt (cosh_pos _)
  · apply DifferentiableAt.log
    apply DifferentiableAt.div
    simp only [differentiableAt_id', DifferentiableAt.div_const, DifferentiableAt.sinh]
    simp only [differentiableAt_id', DifferentiableAt.div_const, DifferentiableAt.cosh]
    exact ne_of_gt (cosh_pos _)
    apply div_ne_zero
    exact h''
    exact ne_of_gt (cosh_pos _)
  · simp only [differentiableAt_const]
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  · apply DifferentiableAt.div_const
    apply DifferentiableAt.log
    apply DifferentiableAt.div
    simp only [differentiableAt_id', DifferentiableAt.div_const, DifferentiableAt.sinh]
    simp only [differentiableAt_id', DifferentiableAt.div_const, DifferentiableAt.cosh]
    exact ne_of_gt (cosh_pos _)
    apply div_ne_zero
    exact h''
    exact ne_of_gt (cosh_pos _)
  · apply DifferentiableAt.div_const
    apply DifferentiableAt.log
    apply DifferentiableAt.div
    simp only [differentiableAt_const, differentiableAt_cosh, DifferentiableAt.add]
    simp only [differentiableAt_sinh]
    exact h'
    exact ineq