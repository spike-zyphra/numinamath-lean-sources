import Mathlib

theorem algebra_9287 {f : ℝ → ℝ} (hf : f = λ x => Real.log x / x) :
    StrictMonoOn f (Set.Ioo 0 (Real.exp 1)) := by
-- Show f(x) is strictly monotone by calculating its deriv.
  apply strictMonoOn_of_deriv_pos
  · -- Show that interval $(0,e)$ is convex.
    exact convex_Ioo _ _
  · -- Show that f(x) is continuous on $(0,e)$.
    rw [hf]
    apply ContinuousOn.div₀
    · intro x hx
      apply ContinuousWithinAt.log
      · apply continuousWithinAt_id
      · simp at hx
        linarith
    · apply continuousOn_id'
    · intro x hx
      simp at hx
      linarith
  · -- Show that f'(x) is positive on $(0,e)$.
    intro x hx
    simp at hx
    rcases hx with ⟨hx₁, hx₂⟩
    rw [hf, deriv_div (by apply Real.differentiableAt_log; linarith) (by apply differentiableAt_id) (by linarith), Real.deriv_log, deriv_id'', mul_one, inv_mul_cancel₀ (by linarith), div_pos_iff]
    left
    refine ⟨?_, by positivity⟩
    have h8 : Real.log x < 1 := by
      have h9 : Real.log x < Real.log (Real.exp 1) := by
        apply Real.log_lt_log
        linarith
        linarith
      have h10 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      linarith [h10, h9]
    linarith [h8]