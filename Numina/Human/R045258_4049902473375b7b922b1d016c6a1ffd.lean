import Mathlib

open Topology Filter Real

/- ## Problem Statement

Calculate the limit of the function:

$\lim _{x \rightarrow 0} \frac{2^{3 x}-3^{5 x}}{\sin 7 x-2 x}$ -/
theorem calculus_137647 :
    Tendsto (λ x => (2^(3*x) - 3^(5*x))/(Real.sin (7*x) - 2*x)) (𝓝[≠] 0) (𝓝 (Real.log (2^3/3^5)/5)) := by
  -- Prove an auxiliary lemma:
  -- the derivative of a^(b * x) is a^(b * x) * log a * b for all 0 < a.
  have rpow_deriv {a b x : ℝ} (ha : 0 < a) : HasDerivAt (fun x => a ^ (b * x)) (a ^ (b * x) * log a * b) x := by
    apply HasDerivAt.comp
    · apply HasStrictDerivAt.hasDerivAt
      apply hasStrictDerivAt_const_rpow ha
    · nth_rw 2 [← mul_one b]
      apply HasDerivAt.const_mul
      exact hasDerivAt_id' x
  -- Apply L'Hôpital's rule to (2^(3 * x) - 3^(5 * x)) / (sin(7 * x) - 2 * x).
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => 2^(3 * x) * log 2 * 3 - 3^(5 * x) * log 3 * 5) (g' := fun x => cos (7 * x) * (7 * 1) - 2 * 1)
  -- Show that the derivative of 2^(3 * x) - 3^(5 * x) is 2^(3 * x) * log 2 * 3 - 3^(5 * x) * log 3 * 5.
  · apply Eventually.of_forall
    intro x
    apply HasDerivAt.sub
    · apply rpow_deriv (by norm_num)
    · apply rpow_deriv (by norm_num)
  -- Show that the derivative of sin(7 * x) - 2 * x is cos(7 * x) * 7 - 2.
  · apply Eventually.of_forall
    intro x
    apply HasDerivAt.sub
    · apply HasDerivAt.sin
      apply HasDerivAt.const_mul
      exact hasDerivAt_id' x
    · apply HasDerivAt.const_mul
      exact hasDerivAt_id' x
  -- Show that cos(7 * x) * 7 - 2 ≠ 0 in a neighborhood of 0.
  -- It is enough to show that cos(7 * x) * 7 - 2 > 0 in a neighborhood of 0.
  · suffices ∀ᶠ (x : ℝ) in 𝓝[≠] 0, 0 < cos (7 * x) * (7 * 1) - 2 * 1 by
      apply this.mono
      intro x h
      exact ne_of_gt h
    -- Show that lim (cos (7 * x) * 7 - 2) = 5 > 0 as x tends to 0.
    apply Tendsto.eventually_const_lt (v := 5) (by norm_num)
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    rw [show 5 = cos (7 * 0) * (7 * 1) - 2 * 1 by norm_num]
    apply Continuous.tendsto
    fun_prop
  -- Show that lim(2^(3 * x) - 3^(5 * x)) = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show (0 : ℝ) = 2 ^ (3 * 0 : ℝ) - 3 ^ (5 * 0 : ℝ) by simp]
    apply ContinuousAt.tendsto
    apply ContinuousAt.sub
    · apply ContinuousAt.rpow (by fun_prop) (by fun_prop) (by norm_num)
    · apply ContinuousAt.rpow (by fun_prop) (by fun_prop) (by norm_num)
  -- Show that lim(sin(7 * x) - 2 * x) = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show (0 : ℝ) = sin (7 * 0) - 2 * 0 by simp]
    apply Continuous.tendsto
    fun_prop
  -- We have log(2^3 / 3^5) = (2^0 * log 2 * 3 - 3^0 * log 3 * 5) / (cos(0) * 7 - 2).
  have eq : log (2 ^ 3 / 3 ^ 5) / 5 = (2 ^ (3 * 0 : ℝ) * log 2 * 3 - 3 ^ (5 * 0 : ℝ) * log 3 * 5) / (cos (7 * 0) * (7 * 1) - 2 * 1) := by
    simp [log_div]
    ring
  rw [eq]
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  -- It is left to show that the function (2^(3 * x) * log 2 * 3 - 3^(5 * x) * log 3 * 5) / (cos(7 * x) * 7 - 2))
  -- is continuous at 0.
  apply ContinuousAt.tendsto
  apply ContinuousAt.div _ (by fun_prop) (by norm_num)
  apply ContinuousAt.sub
  · apply ContinuousAt.mul _ (by fun_prop)
    apply ContinuousAt.mul _ (by fun_prop)
    apply ContinuousAt.rpow (by fun_prop) (by fun_prop) (by norm_num)
  · apply ContinuousAt.mul _ (by fun_prop)
    apply ContinuousAt.mul _ (by fun_prop)
    apply ContinuousAt.rpow (by fun_prop) (by fun_prop) (by norm_num)