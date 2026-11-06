import Mathlib

open Real Set
open scoped BigOperators

/- EXAMPLE 2. Calculate the definite integral
$$
\int_{0}^{\arccos (1 / \sqrt{6})} \frac{3 \tan^{2} x-1}{\tan^{2} x+5} d x
$$
 -/
theorem calculus_151402 : ∫ x in (0)..(arccos (1 / sqrt 6)), (3 * tan x ^ 2 - 1) / (tan x ^ 2 + 5) =
    Real.pi / Real.sqrt 5 - arctan (Real.sqrt 5) := by
  -- We have 0 = arctan 0.
  rw [show 0 = arctan 0 by simp]
  -- Show that arccos (1 / √6) = arctan √5.
  have eq : arccos (1 / √6) = arctan (√5) := by
    -- It is enough to show that tan (arccos (1 / √6)) = tan (arctan √5) = √5.
    -- This follows from 0 < arccos (1 / √6) < π / 2.
    apply tan_inj_of_lt_of_lt_pi_div_two
    · linarith [arccos_nonneg (1 / √6), pi_pos]
    · rw [arccos_lt_pi_div_two]
      positivity
    · exact neg_pi_div_two_lt_arctan _
    · exact arctan_lt_pi_div_two _
    -- tan (arccos (1 / √6)) = √(1 - 1 / √6) * √6 = √5.
    rw [tan_arctan, tan_arccos]
    simp
    rw [← sqrt_mul (by norm_num)]
    norm_num
  rw [eq]
  -- Change the integral variable with x = arctan t.
  rw [← intervalIntegral.integral_comp_smul_deriv' (fun x _ => hasDerivAt_arctan x)]
  rotate_left
  · -- Show that 1 / (1 + x^2) is continuous.
    fun_prop (disch := intros; positivity)
  · -- Show that (3 * tan x^2 - 1) / (tan x^2 + 5) is continuous
    -- on arctan '' [0, √5].
    -- Prove that tan x^2 is continuous on this interval.
    have h : ContinuousOn (fun x => tan x^2) (arctan '' uIcc 0 √5) := by
      intro y
      simp only [sqrt_nonneg, uIcc_of_le, mem_image, mem_Icc, forall_exists_index, and_imp]
      intro x hx1 hx2 hxy
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.pow
      rw [continuousAt_tan]
      -- It is enough to show that cos y ≠ 0 for y = arctan x.
      -- cos (arctan x) = 1 / √(1 + x^2) ≠ 0 for all x.
      rw [← hxy, cos_arctan]
      positivity
    apply ContinuousOn.div
    · apply ContinuousOn.sub _ (by fun_prop)
      apply ContinuousOn.mul (by fun_prop) h
    · apply ContinuousOn.add h (by fun_prop)
    · -- Show that tax x^2 + 5 ≠ 0 for x ∈ arctan '' [0, √5].
      simp only [sqrt_nonneg, uIcc_of_le, mem_image, mem_Icc, ne_eq, forall_exists_index, and_imp]
      intro y x hx1 hx2 hxy
      simp [← hxy]
      positivity
  -- Show that the function under the integral is equal to
  -- (4 / 5) * (1 / (1 + (x / √5)^2)) - 1 / (1 + x^2))
  -- and find its integral on [0, √5].
  rw [intervalIntegral.integral_congr
      (g := fun x => (4 / 5) * (1 / (1 + (x / √5)^2)) - 1 / (1 + x^2))]
  swap
  · intro x
    simp only [sqrt_nonneg, uIcc_of_le, mem_Icc, one_div, Function.comp_apply, tan_arctan,
      smul_eq_mul, and_imp]
    intro hx1 hx2
    field_simp
    ring
  rw [intervalIntegral.integral_sub _ (by simp)]
  swap
  · apply Continuous.intervalIntegrable
    fun_prop (disch := intros; positivity)
  -- The integral of 1 / (1 + x^2) on [0, √5] is arctan √5 - arctan 0 = arctan √5.
  rw [integral_one_div_one_add_sq, intervalIntegral.integral_const_mul]
  -- We have ∫ x in (0)..√5, 1 / (1 + (x / √5)^2)
  --          = √5 * ∫ x in (0)..1, 1 / (1 + x^2)
  --          = √5 * (arctan 1 - arctan 0) = √5 * π / 4.
  rw [intervalIntegral.integral_comp_div (f := fun x => 1 / (1 + x^2)) (by positivity)]
  rw [integral_one_div_one_add_sq]
  simp
  rw [show 4 / 5 * (√5 * (π / 4)) = (√5 / 5) * π by ring]
  nth_rw 2 [show 5 = √5 * √5 by simp]
  field_simp
  ring_nf
  simp [mul_comm]