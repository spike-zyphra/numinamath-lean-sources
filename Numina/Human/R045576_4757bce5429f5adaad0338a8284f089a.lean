import Mathlib

open Topology Filter Real

/- ## Problem Statement
Based on the definition of the derivative, find $f^{\prime}(0)$:
$$
f(x)=\left\{\begin{array}{c}
\frac{\cos x-\cos 3 x}{x}, x \neq 0 \\
0, x=0
\end{array}\right.
$$
 -/
theorem calculus_139644 (f : ℝ → ℝ)
    (h₀ : ∀ x, x ≠ 0 → f x = (Real.cos x - Real.cos (3 * x)) / x)
    (h₁ : f 0 = 0) :
    deriv f 0 = 4 := by
  -- Rewrite the goal as HasDerivAt f 4 0.
  apply HasDerivAt.deriv
  -- Use the definition of the derivative and get the following goal:
  -- lim (x⁻¹ * f(x)) = 4 as x tends to 0.
  simp [hasDerivAt_iff_tendsto_slope, slope_fun_def, h₁]
  -- Define s = {0}ᶜ.
  set s : Set ℝ := {0}ᶜ
  -- We have s ∈ 𝓝[≠] 0.
  have hs : s ∈ 𝓝[≠] 0 := self_mem_nhdsWithin
  -- If x ∈ s then x ≠ 0.
  have hsx {x} (hx : x ∈ s) : x ≠ 0 := hx
  -- Show that x⁻¹ * f x = (-1 / 2) * (sin ((1 / 2) * x) / ((1 / 2) * x))^2 + (9 / 2) * (sin ((3 / 2) * x) / ((3 / 2) * x))^2)
  -- for all x ≠ 0.
  have eq : (fun x => (-1 / 2) * (sin ((1 / 2) * x) / ((1 / 2) * x))^2 + (9 / 2) * (sin ((3 / 2) * x) / ((3 / 2) * x))^2)
        =ᶠ[𝓝[≠] 0] (fun x => x⁻¹ * f x) := by
    simp_rw [EventuallyEq, eventually_iff_exists_mem]
    use s, hs
    intro x hx
    rw [h₀ x hx]
    -- We have cos x = cos (2 * (x / 2)) = 1 - 2 * sin (x / 2)^2 and
    -- cos(3 * x) = cos(2 * (3 * x / 2)) = 1 - 2 * sin ((3 / 2) * x)^2.
    conv => rhs; rhs; lhs; rw [show x = 2 * (x / 2) by ring, show 3 * (2 * (x / 2)) = 2 * ((3 / 2) * x) by ring]
    have hcos2 y : cos (2 * y) = 1 - 2 * sin y ^ 2 := by linarith [sin_sq_eq_half_sub y]
    rw [hcos2, hcos2]
    ring_nf
  apply Tendsto.congr' eq
  -- Prove that lim (sin(a * x) / (a * x)) = 1 as x tends to 0 for all a ≠ 0.
  have hsin {a : ℝ} (ha : a ≠ 0) : Tendsto (fun x => sin (a * x) / (a * x)) (𝓝[≠] 0) (𝓝 1) := by
    -- Apply L'Hôpital's rule.
    apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => cos (a * x) * a) (g' := fun x => a * 1)
    -- Show that the derivative of sin(a * x) is cos(a * x) * a.
    · rw [eventually_iff_exists_mem]
      use s, hs
      intro x hx
      apply HasDerivAt.sin
      nth_rw 2 [show a = a * 1 by ring]
      apply HasDerivAt.const_mul
      exact hasDerivAt_id' x
    -- Show that the derivative of a * x  is a.
    · rw [eventually_iff_exists_mem]
      use s, hs
      intro x hx
      apply HasDerivAt.const_mul
      exact hasDerivAt_id' x
    -- Show that a ≠ 0.
    · simp [ha]
    -- Show that lim sin(a * x) = 0 as x tends to 0.
    · apply Tendsto.mono_left _ nhdsWithin_le_nhds
      nth_rw 2 [show 0 = sin (a * 0) by simp]
      apply Continuous.tendsto
      fun_prop
    -- Show that lim (a * x) = 0 as x tends to 0.
    · apply Tendsto.mono_left _ nhdsWithin_le_nhds
      nth_rw 2 [show 0 = a * 0 by simp]
      apply Continuous.tendsto
      fun_prop
    -- Show that lim cos (a * x) * a / a = 1 as x tends to 0.
    · apply Tendsto.mono_left _ nhdsWithin_le_nhds
      nth_rw 2 [show 1 = cos (a * 0) * a / (a * 1) by field_simp]
      apply Continuous.tendsto
      fun_prop
  -- It is left to show that the limit of
  -- -1 / 2 * (sin (1 / 2 * x) / (1 / 2 * x)) ^ 2 + 9 / 2 * (sin (3 / 2 * x) / (3 / 2 * x)) ^ 2
  -- is 4 as x tends to 0.
  -- We have lim(sin (a * x) / (a * x)) = 1 as x tends to 0, so the limit of this function is
  -- -1 / 2 + 9 / 2 = 4.
  rw [show (4 : ℝ) = (-1 / 2) * 1^2 + (9 / 2) * 1^2 by norm_num]
  apply Tendsto.add <;> apply Tendsto.const_mul <;> apply Tendsto.pow <;> apply hsin (by norm_num)