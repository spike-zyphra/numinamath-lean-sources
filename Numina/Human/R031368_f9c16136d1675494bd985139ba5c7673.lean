import Mathlib

open Real Set
open scoped BigOperators
open Polynomial

/- The monotonic increasing interval of the function $f(x) = \ln(-x^2 + 2x + 8)$ is (-2, 1]. -/
theorem algebra_9309 {f : ℝ → ℝ} (hf : f = λ x => log ((-X^2 + 2 * X + 8).eval x)) :
  MonotoneOn f (Set.Ioc (-2) 1) := by
  -- Let $u(x) = -x^2 + 2x + 8$, the increasing interval of $u(x)$ is $(-2, 1]$.
  have ux_strict_mono : StrictMonoOn (fun (x : ℝ) => (-X^2 + 2 * X + 8).eval x) (Set.Icc (-2) 1) := by
    apply strictMonoOn_of_deriv_pos
    -- proof of icc is convex
    .
      apply convex_Icc
    -- prrof of $-x^2 + 2x + 8$ is continuous on $(-2, 1])
    .
      apply Polynomial.continuousOn
    -- proof of deriv of $-x^2 + 2x + 8$ is larger than zero
    .
      intro x hx
      rw [Polynomial.deriv]
      simp
      simp at hx
      linarith
  rw [hf]
  intro x hx y hy hxy
  simp
  -- log is monotone on $(0, +\inf)$
  apply Real.log_le_log
  . -- proof of $0 < -x ^ 2 + 2 * x + 8$
    have neg2 : (-2) ∈ Icc (-2) (1 : ℝ) := by
      simp
      linarith
    have xltneg2 : -2 < x := by
      simp at hx
      exact hx.1
    have hs := ux_strict_mono (neg2) (Set.mem_Icc_of_Ioc hx) (xltneg2)
    simp at hs
    norm_num at hs
    linarith
  . -- proof of $-x ^ 2 + 2 * x + 8 ≤ -y ^ 2 + 2 * y + 8$
    have m := ux_strict_mono.monotoneOn (Set.mem_Icc_of_Ioc hx) (Set.mem_Icc_of_Ioc hy) hxy
    simp at m; simp
    exact m
