import Mathlib

open Real Set
open scoped BigOperators

/- ## Problem Statement

Calculate the definite integral:


$$

\int_{0}^{\frac{\pi}{2}} \frac{\sin ^{2} x d x}{(1+\cos x+\sin x)^{2}}

$$
 -/
theorem calculus_142171 : ∫ x in (0)..(π/2), sin x ^ 2 / (1 + cos x + sin x) ^ 2 =
    1/2 - 1/2 * log 2 := by
  -- Show that 0 < sin x + cos x for x ∈ [0, π / 2].
  have ineq1 {x} (hx1 : 0 ≤ x) (hx2 : x ≤ π / 2) : 0 < sin x + cos x := by
    -- If x = 0 then sin 0 + cos 0 = 1 > 0.
    by_cases h : x = 0
    · simp [h]
    -- If x ≠ 0 then show that 0 < sin x and 0 ≤ cos x.
    apply add_pos_of_pos_of_nonneg
    · apply sin_pos_of_pos_of_lt_pi _ (by linarith [pi_pos])
      rw [lt_iff_le_and_ne]
      exact ⟨hx1, Ne.symm h⟩
    · apply cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  -- Show that the derivative of (log (tan (x / 2) ^ 2 + 1) / 2 - log (tan (x / 2) + 1) - 1 / (1 + tan (x / 2))) is
  -- equal to sin x ^ 2 / (1 + cos x + sin x) ^ 2 for all x ∈ [0, π / 2].
  have hd x (hx : x ∈ Icc 0 (π / 2)) : HasDerivAt ((fun x => log (x ^ 2 + 1) / 2 - log (x + 1) - 1 / (1 + x)) ∘ (fun x => tan (x / 2))) (sin x ^ 2 / (1 + cos x + sin x) ^ 2) x := by
    simp only [mem_Icc] at hx
    -- Define f(x) = log (x ^ 2 + 1) / 2 - log (x + 1) - 1 / (1 + x)
    set f : ℝ → ℝ := fun x => _ - _ - _
    -- Define f'(x) = x / (x ^ 2 + 1) - 1 / (x + 1) + 1 / (x + 1) ^ 2
    set f' := fun x : ℝ => x / (x ^ 2 + 1) - 1 / (x + 1) - -1 / (x + 1) ^ 2
    -- Prove several auxiliary inequalities.
    have ineqs : cos (x / 2) ≠ 0 ∧ sin (x / 2) + cos (x / 2) ≠ 0 ∧ 1 + cos x + sin x ≠ 0 := by
      constructorm* _ ∧ _
      · apply ne_of_gt
        apply cos_pos_of_mem_Ioo
        simp only [mem_Ioo]
        constructor <;> linarith [pi_pos]
      · apply ne_of_gt
        apply ineq1 (by linarith) (by linarith)
      · linarith [ineq1 hx.1 hx.2]
    -- Demonstrate that the derivative of f(t) is f'(t) for all t ∈ [0, 1].
    have hf {t} (ht1 : 0 ≤ t) (ht2 : t ≤ 1) : HasDerivAt f (f' t) t := by
      -- The result follows from basic properties of derivatives.
      apply HasDerivAt.sub
      · apply HasDerivAt.sub
        · rw [show t / (t ^ 2 + 1) = 2 * t ^ 1 / (t ^ 2 + 1) / 2 by ring]
          apply HasDerivAt.div_const
          apply HasDerivAt.log _ (by positivity)
          apply HasDerivAt.add_const
          apply hasDerivAt_pow
        · apply HasDerivAt.log _ (by linarith)
          apply HasDerivAt.add_const
          exact hasDerivAt_id' t
      · apply HasDerivAt.comp_const_add
        rw [show -1 = 0 * (1 + t) - 1 * 1 by ring, add_comm t]
        apply HasDerivAt.div (hasDerivAt_const (1 + t) 1) (hasDerivAt_id' (1 + t))
        linarith
    -- Show that f'(tan(x / 2)) * 1 / (2 * cos (x / 2) ^ 2) = sin x ^ 2 / (1 + cos x + sin x) ^ 2.
    have eq : sin x ^ 2 / (1 + cos x + sin x) ^ 2 = f' (tan (x / 2)) * 1 / (2 * cos (x / 2) ^ 2) := by
      -- Rewrite tan(x / 2) as sin(x / 2) / cos(x / 2).
      simp only [tan_eq_sin_div_cos, mul_one, f']
      field_simp [ineqs]
      -- Rewrite sin(x) as 2 * sin(x / 2) * cos(x / 2).
      rw [show sin x = 2 * sin (x / 2) * cos (x / 2) by rw [← sin_two_mul]; ring_nf]
      -- Rewrite cos(x) as cos(x / 2) ^ 2 - sin(x / 2).
      rw [show cos x = cos (x / 2) ^ 2 - sin (x / 2) ^ 2 by rw [← cos_two_mul']; ring_nf]
      -- The result is just a linear combination of sin(x / 2)^2 + cos(x / 2)^2 = 1.
      -- (Use polyrith to find the correct coefficients.)
      linear_combination
        (-(1 * sin (x / 2) ^ 6 * cos (x / 2) ^ 2) + sin (x / 2) ^ 5 * cos (x / 2) ^ 3 +
                            8 * sin (x / 2) ^ 4 * cos (x / 2) ^ 4 +
                          8 * sin (x / 2) ^ 3 * cos (x / 2) ^ 5 +
                        sin (x / 2) ^ 2 * cos (x / 2) ^ 6 -
                      1 * sin (x / 2) * cos (x / 2) ^ 7 +
                    2 * sin (x / 2) ^ 4 * cos (x / 2) ^ 2 -
                  4 * sin (x / 2) ^ 2 * cos (x / 2) ^ 4 -
                2 * sin (x / 2) * cos (x / 2) ^ 5 -
              1 * sin (x / 2) ^ 2 * cos (x / 2) ^ 2 -
            1 * sin (x / 2) * cos (x / 2) ^ 3) *
          (sin_sq_add_cos_sq (x / 2))
    rw [eq]
    -- It is left to show that the derivative of f(tan(x / 2)) is f'(tan(x / 2)) * 1 / (2 * cos(x / 2)^2).
    apply HasDerivAt.comp
    · rw [mul_one]
      -- We already proved that the derivative of f(t) is f'(t) for t ∈ [0, 1].
      -- It is left to show that tan(x / 2) ∈ [0, 1].
      apply hf
      · rw [← tan_pi_div_four]
        apply strictMonoOn_tan.monotoneOn _ _ (by linarith)
        · simp; constructor <;> linarith [pi_pos]
        · simp; constructor <;> linarith [pi_pos]
      · apply tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)
    -- Show that the derivative of tan(x / 2) is 1 / (2 * cos(x / 2)^2).
    · rw [show (2 * cos (x / 2) ^ 2)⁻¹ = 1 / cos (x / 2) ^ 2 * (1 / 2) by ring]
      rw [show (fun x => tan (x / 2)) = tan ∘ (fun x => x / 2) by ext x; simp]
      apply HasDerivAt.comp
      · apply hasDerivAt_tan
        simp [ineqs]
      · apply HasDerivAt.div_const
        exact hasDerivAt_id' x
  have hucc : uIcc 0 (π / 2) = Icc 0 (π / 2) := by rw [uIcc_of_le (by positivity)]
  -- We found a function f such that f'(x) = sin(x)^2 / (1 + cos x + sin x)^2.
  -- So the integral is equal to f(π / 2) - f(0).
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by positivity) _ (fun x hx => hd x (mem_Icc_of_Ioo hx))]
  -- Show that f(π / 2) - f(0) = 1 / 2 - 1 / 2 * log(2).
  · simp [show π / 2 / 2 = π / 4 by ring, show 1 + 1 = (2 : ℝ) by norm_num]
    ring
  -- We also need to show that sin(x)^2 / (1 + cos x + sin x)^2 is integrable on [0, π / 2].
  -- It is enough to show that this function is continuous on [0, π / 2].
  · apply ContinuousOn.intervalIntegrable
    rw [hucc]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    simp only [mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, and_imp]
    intro x hx1 hx2
    apply ne_of_gt
    linarith [ineq1 hx1 hx2]
  -- We need to show that the derivative f(x) is continuous on [0, π / 2].
  -- This follows from the fact that f is differentiable for all x ∈ [0, π / 2].
  · apply HasDerivAt.continuousOn hd