import Mathlib

/- The monotonic decreasing interval of the function $f(x)= \frac {\ln x}{x}$ is ______.-/
theorem algebra_9096 {f : ℝ → ℝ} (hf : f = λ x => Real.log x / x) :
    AntitoneOn f (Set.Ioi (Real.exp 1)) := by
  -- It's obvious that $x≠0$ since $e < x$.
  have ne_of_gt_exp {x : ℝ} (hx : Real.exp 1 < x) : x ≠ 0 := by
    have : 0 < Real.exp 1 := by positivity
    linarith
  -- Show f(x) is antitone by calculating its deriv.
  apply antitoneOn_of_deriv_nonpos
  -- Show that interval $[e,+\infty)$ is convex.
  . exact convex_Ioi _
  -- Show that f(x) is continuous on $[e,+\infty)$.
  . rw [hf]
    apply ContinuousOn.div₀
    . intro x hx
      apply ContinuousWithinAt.log
      . apply continuousWithinAt_id
      . simp at hx
        exact ne_of_gt_exp hx
    . apply continuousOn_id'
    . intro x hx
      simp at hx
      exact ne_of_gt_exp hx
  -- Show that f(x) is differentiable on $(e,+\infty)$.
  . rw [hf]
    apply DifferentiableOn.div
    . intro x hx
      apply DifferentiableWithinAt.log
      . apply differentiableWithinAt_id
      . simp at hx
        exact ne_of_gt_exp hx
    . apply differentiableOn_id'
    . intro x hx
      simp at hx
      exact ne_of_gt_exp hx
  -- Show that f'(x) is nonpos on $(e,+\infty)$.
  intro x hx
  simp at hx
  have := ne_of_gt_exp hx
  rw [hf, deriv_div (by apply Real.differentiableAt_log; assumption)
    (by apply differentiableAt_id) (by assumption), Real.deriv_log, deriv_id'', mul_one,
    inv_mul_cancel₀ (by assumption)]
  have : 0 < Real.exp 1 := by positivity
  have : 0 < x := by linarith
  rw [div_nonpos_iff]
  right
  have := Real.strictMonoOn_log
  refine ⟨?_, by positivity⟩
  suffices 1 < Real.log x by linarith
  rw [← Real.log_exp 1]
  apply Real.strictMonoOn_log
  . simpa
  . simpa
  . assumption
