import Mathlib

open Function

/-Let $f$ be a function such that $f(0)=1, f^{\prime}(0)=2$, and

$$
f^{\prime \prime}(t)=4 f^{\prime}(t)-3 f(t)+1
$$

for all $t$. Compute the 4th derivative of $f$, evaluated at 0 .-/
theorem calculus_608634 (f : ℝ → ℝ) (df : ContDiff ℝ ⊤ f) (f0 : f 0 = 1)
(df0 : deriv f 0 = 2) (hf : ∀ t, deriv^[2] f t = 4 * deriv f t - 3 * f t + 1) : deriv^[4] f 0 = 54 := by
-- Take derivate on both sides of $hf$ to get the third derivative of $f$  
  have d3f : ∀ t, deriv^[3] f t = 4 * deriv^[2] f t - 3 * deriv f t := by
    intro t; rw [iterate_succ_apply']; nth_rw 1 [funext_iff.mpr hf, deriv_add_const]
    rw [deriv_sub, deriv_const_mul, deriv_const_mul, iterate_succ_apply', iterate_one]
    · exact (df.differentiable (by simp)).differentiableAt
    · rw [← iterate_one (deriv), ← iteratedDeriv_eq_iterate]
      exact (df.differentiable_iteratedDeriv 1 (by simp)).differentiableAt
    · apply DifferentiableAt.const_mul; rw [← iterate_one (deriv), ← iteratedDeriv_eq_iterate]
      exact (df.differentiable_iteratedDeriv 1 (by simp)).differentiableAt
    apply DifferentiableAt.const_mul; exact (df.differentiable (by simp)).differentiableAt
-- Take derivate on both sides of $d3f$ to get the fourth derivative of $f$   
  have d4f : ∀ t, deriv^[4] f t = 4 * deriv^[3] f t - 3 * deriv^[2] f t := by
    intro t; rw [iterate_succ_apply']; nth_rw 1 [funext_iff.mpr d3f]
    rw [deriv_sub, deriv_const_mul, deriv_const_mul]
    nth_rw 2 [iterate_succ_apply']; nth_rw 3 [iterate_succ_apply']; rw [iterate_one]
    · rw [← iterate_one (deriv), ← iteratedDeriv_eq_iterate]
      exact (df.differentiable_iteratedDeriv 1 (by simp)).differentiableAt
    · rw [← iteratedDeriv_eq_iterate]
      exact (df.differentiable_iteratedDeriv 2 (WithTop.natCast_lt_top 2)).differentiableAt
    · apply DifferentiableAt.const_mul; rw [← iteratedDeriv_eq_iterate]
      exact (df.differentiable_iteratedDeriv 2 (WithTop.natCast_lt_top 2)).differentiableAt
    apply DifferentiableAt.const_mul;rw [← iterate_one (deriv), ← iteratedDeriv_eq_iterate]
    exact (df.differentiable_iteratedDeriv 1 (by simp)).differentiableAt
-- Plug in $t=0$ to hf, d3f and d4f to find the value of $deriv^[4] 0$
  specialize hf 0; specialize d3f 0; specialize d4f 0
  rw [f0, df0] at hf; norm_num1 at hf
  rw [hf, df0] at d3f; norm_num1 at d3f
  rw [d4f, d3f, hf]; norm_num