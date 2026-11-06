import Mathlib

open Real

/- ## Problem Statement

Calculate the definite integral:

$$
\int_{\pi}^{2 \pi} \frac{1-\cos x}{(x-\sin x)^{2}} d x
$$
 -/
theorem calculus_141664 : ∫ x in (π)..(2*π), (1 - cos x)/(x - sin x)^2 = 1/(2*π) := by
  -- Prove an auxiliary inequality: x - sin x ≠ 0 for x ∈ [π, 2π].
  have hsin0 x (hx : x ∈ Set.Icc π (2 * π)) : x - sin x ≠ 0 := by
    apply ne_of_gt
    simp only [Set.mem_Icc] at hx
    -- This inequality follows from 3.14 < π and sin x ≤ 1.
    linarith [Real.pi_gt_d2 , Real.sin_le_one x]
  -- Show that the derivative of -1 / (x - sin x) is (1 - cos x) / (x - sin x)^2 for all x ∈ [π, 2π].
  have hd x (hx : x ∈ Set.Icc π (2 * π)) : HasDerivAt (fun x => -1 / (x - sin x)) ((1 - cos x) / (x - sin x)^2) x := by
    simp_rw [neg_div, one_div, show (1 - cos x) / (x - sin x)^2 = -(-(1 - cos x) / (x - sin x)^2) by ring]
    apply HasDerivAt.neg
    apply HasDerivAt.inv
    · exact HasDerivAt.sub (hasDerivAt_id' x) (hasDerivAt_sin x)
    · exact hsin0 x hx
  -- We have π ≤ 2 * π.
  have ineq : π ≤ 2 * π := by linarith [Real.pi_pos]
  -- Apply the fundamental theorem of calculus to (-1 / (x - sin x))' = (1 - cos x) / (x - sin x)^2
  -- and obtain ∫ x in (π)..(2*π), (1 - cos x)/(x - sin x)^2 = -1 / (2π - sin 2π) + 1 / (π - sin π).
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ineq _ (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))]
  -- It is easy to show that -1 / (2π - sin 2π) + 1 / (π - sin π) = 1 / 2π.
  · simp; ring
  -- We need to show that (1 - cos x)/(x - sin x)^2 is integrable on [π, 2π].
  -- It is enough to show that this function is continuous on [π, 2π].
  · apply ContinuousOn.intervalIntegrable_of_Icc ineq
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    -- Continuity follows from x - sin x ≠ 0 on [π, 2π].
    · intro x hx
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
      exact hsin0 x hx
  -- We also need to show that -1 / (x - sin x) is continuous on [π, 2π]
  -- It is continuous because it is differentiable at every point in [π, 2π].
  · exact HasDerivAt.continuousOn hd