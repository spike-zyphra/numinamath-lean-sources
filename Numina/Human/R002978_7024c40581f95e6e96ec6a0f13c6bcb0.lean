import Mathlib

open Topology Filter Real

/- ## Problem Statement

Based on the definition of the derivative, find $f^{\prime}(0)$:

$f(x)=\left\{\begin{array}{c}\frac{\ln \left(1+2 x^{2}+x^{3}\right)}{x}, x \neq 0 ; \\ 0, x=0\end{array}\right.$ -/
theorem calculus_138023 {f : ℝ → ℝ}
    (hf : ∀ x, x ≠ 0 → f x = (Real.log (1 + 2 * x ^ 2 + x ^ 3)) / x)
    (hf0 : f 0 = 0) :
    deriv f 0 = 2 := by
  -- Rewrite the goal as HasDerivAt f 2 0.
  apply HasDerivAt.deriv
  -- Use the definition of the derivative and get the following goal:
  -- lim (x⁻¹ * f(x)) = 2 as x tends to 0.
  simp [hasDerivAt_iff_tendsto_slope, slope_fun_def, hf0]
  -- Define s = (-1, 1) \ {0}.
  set s : Set ℝ := Set.Ioo (-1) 1 \ {0}
  -- We have s ∈ 𝓝[≠] 0.
  have hs : s ∈ 𝓝[≠] 0 := by
    unfold s
    rw [Set.diff_eq, Set.inter_comm]
    apply inter_mem_nhdsWithin
    apply Ioo_mem_nhds (by norm_num) (by norm_num)
  -- If x ∈ s then x ≠ 0.
  have hsx0 {x} (hx : x ∈ s) : x ≠ 0 := by
    simp [s] at hx
    exact hx.2
  -- If x ∈ s then 0 < 1 + 2 * x ^ 2 + x ^ 3.
  have hsx {x} (hx : x ∈ s) : 0 < 1 + 2 * x ^ 2 + x ^ 3 := by
    simp [s] at hx
    nlinarith
  -- Show that x⁻¹ * f x = log (1 + 2 * x ^ 2 + x ^ 3) / x ^ 2 for all x ∈ s.
  have eq : (fun x => log (1 + 2 * x ^ 2 + x ^ 3) / x ^ 2) =ᶠ[𝓝[≠] 0] (fun x => x⁻¹ * f x) := by
    simp_rw [EventuallyEq, eventually_iff_exists_mem]
    use s, hs
    intro x hx
    field_simp [hf x (hsx0 hx), pow_two]
  -- It is enough to show that lim (log (1 + 2 * x ^ 2 + x ^ 3) / x ^ 2) = 2 as x tends to 0.
  apply Tendsto.congr' eq
  -- Use L'Hôpital's rule to compute the limit.
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => (4 * x + 3 * x ^ 2) / (1 + 2 * x ^ 2 + x ^ 3)) (g' := fun x => 2 * x)
  -- Show that the derivative of log(1 + 2 * x^2 + x^3) is (4 * x + 3 * x^2) / (1 + 2 * x^2 + x^3).
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    apply HasDerivAt.log
    · simp_rw [add_assoc]
      apply HasDerivAt.const_add
      apply HasDerivAt.add
      · rw [show 4 * x = 2 * (2 * x ^ 1 * 1) by ring]
        apply HasDerivAt.const_mul
        apply HasDerivAt.pow
        exact hasDerivAt_id' x
      · rw [show 3 * x ^ 2 = 3 * x ^ 2 * 1 by ring]
        apply HasDerivAt.pow
        exact hasDerivAt_id' x
    · exact ne_of_gt (hsx hx)
  -- Show that the derivative of x^2 is 2 * x.
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    rw [show 2 * x = 2 * x ^ 1 * 1 by ring]
    apply HasDerivAt.pow
    exact hasDerivAt_id' x
  -- Show that 2 * x ≠ 0 for all x ∈ s.
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    contrapose! hsx0
    use x, hx
    linarith
  -- Show that lim(log(1 + 2 * x^2 + x^3)) = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show 0 = log (1 + 2 * 0 ^ 2 + 0 ^ 3) by simp]
    apply ContinuousAt.tendsto
    fun_prop (disch := simp)
  -- Show that lim (2 * x) = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show (0 : ℝ) = 0 ^ 2 by simp]
    apply ContinuousAt.tendsto
    fun_prop
  -- It is left to prove that
  -- lim (4 * x + 3 * x^2) / (1 + 2 * x^2 + x^3) / (2 * x) = 2 as x tends to 0.
  -- Show that (4 * x + 3 * x^2) / (1 + 2 * x^2 + x^3) / (2 * x) = (2 + 3 / 2 * x) / (1 + 2 * x ^ 2 + x ^ 3)
  -- for all x ∈ s.
  replace eq : (fun x : ℝ => (2 + 3 / 2 * x) / (1 + 2 * x ^ 2 + x ^ 3))
      =ᶠ[𝓝[≠] 0] (fun x : ℝ => (4 * x + 3 * x ^ 2) / (1 + 2 * x ^ 2 + x ^ 3) / (2 * x)) := by
    simp_rw [EventuallyEq, eventually_iff_exists_mem]
    use s, hs
    intro x hx
    have ineq : (1 + 2 * x ^ 2 + x ^ 3) * (2 * x) ≠ 0 := by
      have := hsx0 hx
      have := hsx hx
      positivity
    field_simp [ne_of_gt (hsx hx)]
    ring
  apply Tendsto.congr' eq
  -- The function (2 + 3 / 2 * x) / (1 + 2 * x ^ 2 + x ^ 3) is continuous at 0
  -- so its limit is equal to (2 + 3 / 2 * 0) / (1 + 2 * 0^2 + 0^3) = 2.
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  nth_rw 4 [show (2 : ℝ) = (2 + 3 / 2 * 0) / (1 + 2 * 0^2 + 0^3) by simp]
  apply ContinuousAt.tendsto
  fun_prop (disch := simp)