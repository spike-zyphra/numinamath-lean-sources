import Mathlib
set_option maxHeartbeats 0

open Real intervalIntegral

  /-Evaluate the definite integral $\int_{-1}^{+1} \frac{2 u^{332}+u^{998}+4 u^{1664} \sin u^{691}}{1+u^{666}} \mathrm{~d} u$.-/
  theorem calculus_610864 : ∫ u in (-1 : ℝ)..1,
    (2 * u ^ 332 + u ^ 998 + 4 * u ^ 1664 * sin (u ^ 691)) / (1 + u ^ 666) = 2 / 333 * (1 + π / 4) := by
-- Prove two integrable propositions for later use
  have int1 : IntervalIntegrable (fun u => (2 * u ^ 332 + u ^ 998 + 4 * u ^ 1664 * sin (u ^ 691)) / (1 + u ^ 666)) MeasureTheory.volume (-1) 1 := by
    apply Continuous.intervalIntegrable; apply Continuous.div
    any_goals continuity
    intros; positivity
  have int2 : IntervalIntegrable (fun u => (2 * u ^ 332 + u ^ 998) / (1 + u ^ 666)) MeasureTheory.volume (-1) 1 := by
    apply Continuous.intervalIntegrable; apply Continuous.div
    any_goals continuity
    intros; positivity
-- Splite the integral to two parts and evaluate them seperately
  suffices : ∫ u in (-1 : ℝ)..1,
    (2 * u ^ 332 + u ^ 998) / (1 + u ^ 666) = 2 / 333 * (1 + π / 4) ∧
    ∫ u in (-1 : ℝ)..1, 4 * u ^ 1664 * sin (u ^ 691) / (1 + u ^ 666) = 0
  · rw [← this.left, ← sub_eq_zero, ← integral_sub]
    simp [div_sub_div_same]; exact this.right
    exact int1; exact int2
  constructor
  -- To evaluate the first integral, we first rewrite it to a substitution form
  · suffices : 1 / 333 * ∫ u in (-1:ℝ)..1, ((fun v => (2 + v ^ 2) / (1 + v ^ 2)) ∘ (fun t => t ^ 333)) u * (deriv (fun t => t ^ 333)) u = 2 / 333 * (1 + π / 4)
    · rw [← this, mul_comm, ← integral_mul_const]; apply integral_congr
      intro x hx; simp at hx; simp
      rw [← pow_mul]; norm_num
      rw [mul_assoc, mul_one_div, mul_div_cancel_left₀]
      have : 1 + x ^ 666 ≠ 0 := by positivity
      field_simp; ring; norm_num
  -- Apply the substitution law `integral_comp_mul_deriv'`
    rw [integral_comp_mul_deriv', one_div_mul_eq_div, div_mul_eq_mul_div]
    congr; norm_num
    suffices : ∫ (x : ℝ) in (-1:ℝ)..1, (1 + deriv (fun t => arctan t) x) = 2 * (1 + π / 4)
    · rw [← this]; apply integral_congr
      intro x hx; simp at hx; simp
      have : 1 + x ^ 2 ≠ 0 := by positivity
      field_simp; ring
  -- Use fundamental theorem of calculus `integral_deriv_eq_sub` to evaluate the integral
    rw [integral_add, integral_deriv_eq_sub]; norm_num; ring
    intros; exact differentiable_arctan.differentiableAt
  -- Finish the rest differentiability/integrability/continuity checks
    any_goals simp
    intro x _ _; rw [show 333 * x ^ 332 = deriv (fun t => t ^ 333) x by simp]
    apply DifferentiableAt.hasDerivAt; simp
    apply Continuous.continuousOn; continuity
    apply Continuous.continuousOn; apply Continuous.div
    any_goals continuity
    intros; positivity
-- To evaluate the second integral, we first split the interval $[-1,1]$ to $[-1,0]$ and $[0,1]$
  have int21 : IntervalIntegrable (fun u =>  4 * u ^ 1664 * sin (u ^ 691) / (1 + u ^ 666)) MeasureTheory.volume (-1) 0 := by
    apply Continuous.intervalIntegrable; apply Continuous.div
    any_goals continuity
    intros; positivity
  have int22 : IntervalIntegrable (fun u =>  4 * u ^ 1664 * sin (u ^ 691) / (1 + u ^ 666)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable; apply Continuous.div
    any_goals continuity
    intros; positivity
  rw [← integral_add_adjacent_intervals int21 int22]
-- Use `integral_comp_neg` and `integral_neg` to rewrite the integral, the goal follows
  nth_rw 1 [← neg_zero, ← integral_comp_neg, ← neg_eq_iff_add_eq_zero]
  rw [← integral_neg]; apply integral_congr
  intro x _; simp; rw [Even.neg_pow, Odd.neg_pow, sin_neg]
  rw [Even.neg_pow]; ring; use 333; use 345; norm_num; use 832