import Mathlib

open MeasureTheory intervalIntegral Interval Real

/- Let $T=\int_{0}^{\ln 2} \frac{2 e^{3 x}+e^{2 x}-1}{e^{3 x}+e^{2 x}-e^{x}+1} d x$.
Evaluate $e^{T}$. -/
theorem calculus_608269{T: ℝ}{t: ℝ → ℝ}
  (ht: t = fun x =>
    (2*exp (3*x) + exp (2*x) - 1) / (exp (3*x) + exp (2*x) - exp x + 1))
  (hT: T = ∫ x in (0:ℝ)..(log 2), t x):
  exp T = 11/4 := by
  -- divide the numerator and denominator by e^x.
  have h1: t = fun x =>
    (2*exp (2*x) + exp x - (exp (-x))) / (exp (2*x) + exp x - 1 + exp (-x)) := by
    rw [ht]
    funext x
    have hh1: (2*exp (3*x) + exp (2*x) - 1) = (exp x) *
      (2*exp (2*x) + exp x - (exp (-x))) := by
      simp only [mul_sub, mul_add, ← exp_add,
      add_neg_cancel, exp_zero, sub_left_inj]
      rw [← mul_assoc, mul_comm _ 2, mul_assoc, ← exp_add]
      ring_nf
    have hh2: (exp (3*x) + exp (2*x) - exp x + 1) = (exp x) *
      (exp (2*x) + exp x - 1 + exp (-x)) := by
      simp only [mul_sub, mul_add, ← exp_add, mul_one,
      add_neg_cancel, exp_zero]
      ring_nf
    have hh3: exp x ≠ 0 := exp_ne_zero x
    rw [hh1, hh2]
    exact mul_div_mul_left _ _ hh3
  set f: ℝ → ℝ := fun x => (exp (2*x) + exp x - 1 + exp (-x)) with f_def
  -- some trivial calculation.
  have diff1{x:ℝ}: DifferentiableAt ℝ (fun y => exp (-y)) x := by
    refine DifferentiableAt.exp ?_
    refine Differentiable.differentiableAt differentiable_neg
  have deriv1{x:ℝ}: deriv (fun y => exp (-y)) x = - exp (-x) := by
    rw [_root_.deriv_exp (Differentiable.differentiableAt differentiable_neg)]
    simp only [deriv_neg'', mul_neg, mul_one]
  have diff2x{x:ℝ}: DifferentiableAt ℝ (fun y => 2*y) x := by
    apply DifferentiableAt.const_mul differentiableAt_id'
  have diff2{x:ℝ}: DifferentiableAt ℝ (fun y => exp (2*y)) x := by
    apply DifferentiableAt.exp diff2x
  have deriv2{x:ℝ}: deriv (fun y => exp (2*y)) x = 2 * exp (2*x) := by
    rw [_root_.deriv_exp diff2x, deriv_const_mul 2 differentiableAt_id']
    simp only [deriv_id'', mul_one]
    ring
  have diff3{x:ℝ}: DifferentiableAt ℝ (fun y => (exp (2*y) + exp y - 1)) x := by
    apply DifferentiableAt.sub_const
    apply DifferentiableAt.add diff2 differentiableAt_exp
  have deriv3{x:ℝ}: deriv (fun y => (exp (2*y) + exp y - 1)) x =
    2 * exp (2*x) + exp x := by
    rw [deriv_sub_const, deriv_add diff2 differentiableAt_exp,
    Real.deriv_exp, deriv2]
  have f_diff{x:ℝ}: DifferentiableAt ℝ f x := by
    apply DifferentiableAt.add diff3 diff1
  have pos_log2: log 2 > 0 := by
    apply gt_trans log_two_gt_d9 ?_
    norm_num
  have f'_def: deriv f = fun x => (2*exp (2*x) + exp x - (exp (-x))) := by
    rw [f_def]
    funext x
    rw [deriv_add diff3 diff1, deriv3, deriv1]
    ring
  -- notice that numerator is derivative of the denominator.
  have h2: t = fun x => (deriv f x)/ (f x) := by
    rw [f_def, f'_def, h1]
  simp only [h2] at hT
  -- therefore integral t is integral f' / f = integral ln f.
  have fx_not_zero: ∀x ∈ [[0, log 2]], f x ≠ 0 := by
    intro x hx
    symm; apply ne_of_lt
    simp only [f_def]
    have: exp x - 1 ≥ 0 := by
      apply sub_nonneg.mpr
      apply one_le_exp
      rw [Set.mem_uIcc] at hx
      rcases hx with hx1 | hx2
      · exact hx1.left
      · have := le_trans hx2.left hx2.right
        -- but log 2 > 0, contradiction.
        linarith [this, pos_log2]
    linarith [exp_pos (2*x), this, exp_pos (-x)]
  have h3: ∀x ∈ [[0, log 2]],
    HasDerivAt (fun y => log (f y)) ((fun y => (deriv f y)/ (f y)) x) x :=
    fun x hx =>
    (HasDerivAt.log (DifferentiableAt.hasDerivAt f_diff) (fx_not_zero x hx))
  have h4: IntervalIntegrable (fun y => deriv f y / f y) volume 0 (log 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div ?_ ?_ fx_not_zero
    · simp only [f'_def]
      apply Continuous.continuousOn
      continuity
    · simp only [f_def]
      apply Continuous.continuousOn
      apply Continuous.add ?_ ?_
      · apply Continuous.sub ?_ continuous_const
        apply Continuous.add ?_ continuous_exp
        apply Continuous.rexp ?_
        exact continuous_mul_left 2
      · apply Continuous.rexp continuous_neg
  -- then integral becomes (log f) (log2) - (log f) (0)
  -- and easy to compute the result is log (11/4).
  replace hT: T = log (11/4) := by
    have hh1: (fun y => log (f y)) (log 2) = log (11/2) := by
      simp only [f_def]
      congr 1
      rw [exp_log (by norm_num), mul_comm 2 (log 2), exp_mul,
      exp_log (by norm_num), ← log_inv, exp_log (by norm_num)]
      norm_num
    have hh2: (fun y => log (f y)) 0 = log 2 := by
      simp only [f_def, mul_zero, neg_zero, exp_zero]
      norm_num
    have hh3: log (11/4) = log (11/2) - log 2 := by
      rw [← log_div]
      congr 1
      all_goals norm_num
    rw [hh3, ← hh1]
    nth_rw 2 [← hh2]; rw [hT]
    apply integral_eq_sub_of_hasDerivAt h3 h4
  -- done.
  rw [hT]
  apply exp_log (by norm_num)