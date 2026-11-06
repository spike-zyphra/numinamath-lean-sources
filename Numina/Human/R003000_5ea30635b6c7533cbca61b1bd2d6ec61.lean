import Mathlib

open Real

-- sin (2 * arctan(x)) = 2 * x / (1 + x^2) for all x.
lemma sin_two_mul_arctan (x : ℝ) : sin (2 * arctan x) = 2 * x / (1 + x^2) := by
  -- We have sin(2 * x) = 2 * sin(x) * cos(x),
  -- sin(x) = x / √(1 + x^2),
  -- cos(x) = 1 / √(1 + x^2).
  rw [sin_two_mul, sin_arctan, cos_arctan]
  ring_nf
  rw [inv_pow, sq_sqrt (by positivity)]

/- ## Problem Statement
Calculate the definite integral:
$$
\int_{-\frac{\pi}{2}}^{0} \frac{\cos x \, dx}{(1+\cos x-\sin x)^{2}}
$$
 -/
theorem calculus_142098 : ∫ x in (-π/2)..0, cos x / (1 + cos x - sin x)^2 = -1/2 + log 2 := by
  -- Define f(t) = 2 * arctan(t).
  set f : ℝ → ℝ := fun t => 2 * arctan t
  -- We have f'(t) = 2 / (t^2 + 1).
  have hdf t : HasDerivAt f (2 / (t^2 + 1)) t := by
    rw [show 2 / (t^2 + 1) = 2 * (1 / (1 + t^2)) by ring]
    apply HasDerivAt.const_mul
    exact hasDerivAt_arctan t
  -- We have 0 = f(0) and -π / 2 = f(-1).
  rw [show 0 = f 0 by simp [f]]
  rw [show -π / 2 = f (-1) by simp [f]; ring]
  -- Change the integral variable with x = f(t).
  rw [← intervalIntegral.integral_comp_smul_deriv' (fun t _ => hdf t)]
  rotate_left
  · -- Show that f'(x) = 2 / (x^2 + 1) is continuous on [-1, 0].
    fun_prop (disch := intros; positivity)
  · -- Show that cos x / (1 + cos x - sin x)^2 is continuous on f '' [-1, 0].
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    -- It is enough to show that 1 + cos y - sin y ≠ 0 for x ∈ [-1, 0] and y = f(x).
    simp only [Left.neg_nonpos_iff, zero_le_one, Set.uIcc_of_le, Set.mem_image, Set.mem_Icc, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, forall_exists_index, and_imp]
    intro y x hx1 hx2 eq
    rw [le_iff_lt_or_eq] at hx1
    -- Consider two cases: -1 < x and x = -1.
    cases' hx1 with hx1 hx1
    · -- If -1 < x then it is enough to show that 0 < cos y
      -- (because sin y ≤ 1 for all y).
      suffices 0 < cos y by linarith [sin_le_one y]
      -- Show that -π / 2 < y < π / 2.
      apply cos_pos_of_mem_Ioo
      simp only [Set.mem_Ioo, ← eq, f]
      constructor
      · -- y = 2 * arctan x > 2 * arctan (-1) = 2 * (-π / 4) = -π / 2.
        suffices arctan (-1) < arctan x by
          simp at this
          linarith
        apply arctan_strictMono hx1
      · -- y = 2 * arctan x < 2 * arctan 1 = 2 * (π / 4) = π / 2.
        suffices arctan x < arctan 1 by
          simp at this
          linarith
        apply arctan_strictMono
        linarith
    · -- If x = -1 then y = 2 * arctan (-1) = -π / 2 and
      -- 1 + cos y - sin y = 1 + 0 + 1 = 2 ≠ 0.
      simp [← eq, ← hx1, f, show 2 * (π / 4) = π / 2 by ring]
  simp only [Function.comp_apply, cos_two_mul, cos_sq_arctan, add_sub_cancel,
    sin_two_mul_arctan, smul_eq_mul, f]
  -- Show that the function under the integral is equal to
  -- -(1 / 2 + 1 / (x - 1)) for x ∈ [-1, 0] and show that the integral
  -- ∫ x in (-1)..0, -(1 / 2 + 1 / (x - 1)) = -1/2 + log 2.
  rw [intervalIntegral.integral_congr (g := fun x => -(1 / 2 + 1 / (x - 1)))]
  · rw [intervalIntegral.integral_neg]
    simp
    norm_num [log_div, add_comm]
  intro x
  simp only [Left.neg_nonpos_iff, zero_le_one, Set.uIcc_of_le, Set.mem_Icc, neg_add_rev, and_imp]
  intro hx1 hx2
  field_simp [show x - 1 ≠ 0 by linarith, show 2 - 2 * x ≠ 0 by linarith]
  ring