import Mathlib

open Real Set
open scoped BigOperators

/- 29.24. Prove that $\int_{0}^{\pi / 2} \ln (\sin x) d x=-\frac{\pi}{2} \ln 2$. -/
theorem calculus_229814 : ∫ x in (0)..(π/2), log (sin x) = -π/2 * log 2 := by
  have eqI {b} (hb : (0 : ℝ) ≤ b) : Ι 0 b = Ioc 0 b := Set.uIoc_of_le hb
  -- Prove that log(sin(x)) is integrable on [0, π / 2].
  have hint_sin : IntervalIntegrable (fun x => log (sin x)) MeasureTheory.volume 0 (π / 2) := by
    -- Prove that log(sin(x)) is integrable on [0, 1/16] and on [1/16, π / 2].
    trans 1 / 16
    swap
    -- log(sin(x)) is integrable on [1/16, π / 2] because it is continuous on this interval.
    · apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [pi_gt_d2])
      apply ContinuousOn.log (by fun_prop)
      simp only [mem_Icc, and_imp]
      intro x hx1 hx2
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    -- We show that log(sin(x)) is integrable on [0, 1/16] by showing that
    -- its absolute value is bounded by the integrable function x^(-1/2).
    apply IntervalIntegrable.mono_fun' (g := fun x => x ^ (-1 / 2 : ℝ))
    -- x^r is integrable on any interval when r > -1.
    · apply intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    -- log(sin(x)) is measurable.
    · apply Measurable.aestronglyMeasurable
      apply Measurable.log
      apply Real.measurable_sin
    -- It is left to show that |log(sin(x))| ≤ x^(-1/2) almost everywhere on (0, 1/16].
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
      simp only [eqI (show (0 : ℝ) ≤ 1 / 16 by norm_num), mem_Ioc, norm_eq_abs, and_imp]
      intro x hx1 hx2
      calc
        -- We have |log(sin(x)) = -log(sin(x)) because log(sin(x)) ≤ 0 (0 ≤ sin(x) ≤ 1).
        |log (sin x)| = -log (sin x) := by
            rw [abs_of_nonpos]
            apply log_nonpos _ (sin_le_one _)
            apply sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_gt_d2])
        -- 2 / π * x ≤ sin(x) implies that -log(sin(x)) ≤ -log (2 / π * x) ≤ -log (x / 2)
        -- (because log is increasing and 2 / π ≥ 1 / 2).
        _ ≤ -log (x / 2) := by
            simp only [neg_le_neg_iff]
            apply strictMonoOn_log.monotoneOn (by simp [hx1])
            · simp only [mem_Ioi]
              apply sin_pos_of_pos_of_lt_pi hx1 (by linarith [pi_gt_d2])
            · apply le_trans _ (mul_le_sin (le_of_lt hx1) (by linarith [pi_gt_d2]))
              rw [show x / 2 = (1 / 2) * x by ring]
              apply mul_le_mul_of_nonneg_right _ (by linarith)
              rw [div_le_div_iff₀ (by norm_num) pi_pos]
              linarith [pi_lt_d2]
        -- Show that -log(x / 2) ≤ x^(-1 / 2) for x ∈ (0, 1/16].
        _ ≤ x ^ (-1 / 2 : ℝ) := by
            rw [← sub_nonneg, sub_neg_eq_add]
            -- Let f(x) = x^(-1/2) + log(x / 2).
            -- We need to show that 0 ≤ f(x) for x ∈ (0, 1/16].
            set f := fun x => x ^ (-1 / 2 : ℝ) + log (x / 2)
            trans f (1 / 16)
            -- Show that 0 ≤ f(1/16) ≤ f(x).
            · dsimp [f]
              norm_num [log_div]
              -- f(1/16) = (1/16)^(-1/2) + log(1/32) = 4 - log (2^5) = 4 - 5 * log 2.
              rw [show (32 : ℝ) = 2 ^ 5 by norm_num, log_pow]
              rw [rpow_neg (by norm_num), ← sqrt_eq_rpow, show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num]
              rw [sqrt_sq (by norm_num)]
              -- We have log 2 < 0.694 so 4 - 5 * log 2 > 0.
              linarith [log_two_lt_d9]
            -- Show that f'(x) = (-1 / 2) * x^(-3 / 2) + 1 / x.
            have hf {x} (hx : x ∈ Set.Ioc 0 (1 / 16)) : HasDerivAt f ((-1 / 2) * x ^ (-3 / 2 : ℝ) + 1 / x) x := by
              simp only [mem_Ioc] at hx
              apply HasDerivAt.add
              · rw [show (-3 / 2 : ℝ) = (-1 / 2 - 1) by norm_num]
                apply hasDerivAt_rpow_const (by left; linarith)
              · rw [show 1 / x = (1 / 2) / (x / 2) by ring]
                apply HasDerivAt.log _ (by linarith)
                apply HasDerivAt.div_const (hasDerivAt_id' x)
            -- Show that f'(x) ≤ 0 for x ∈ (0, 1/16). This implies that f is decreasing
            -- on (0, 1/16] and f(1/16) ≤ f(x) follows from 0 < x ≤ 1/16.
            apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 (1 / 16))
            -- f is continuous on (0, 1/16] because it is differentiable.
            · apply HasDerivAt.continuousOn (fun _ hx => hf hx)
            -- f is differentiable on (0, 1/16].
            · simp only [interior_Ioc]
              intro x hx
              apply (hf (mem_Ioc_of_Ioo hx)).differentiableAt.differentiableWithinAt
            -- Show that f'(x) ≤ 0 for x ∈ (0, 1/16).
            · simp only [interior_Ioc]
              intro x hx
              rw [(hf (mem_Ioc_of_Ioo hx)).deriv]
              simp only [mem_Ioo] at hx
              simp_rw [neg_div]
              rw [rpow_neg (by linarith)]
              simp only [one_div, neg_mul, neg_add_le_iff_le_add, add_zero, ← mul_inv]
              -- After simplifications, we get the following goal
              -- 1 / x ≤ 1 / (2 * x ^ (3/2)).
              have hpos : 0 < 2 * x ^ (3 / 2 : ℝ) := by
                apply mul_pos zero_lt_two
                apply rpow_pos_of_pos hx.1
              -- The goal is equivalent to 2 * x^(3 / 2) ≤ x.
              rw [inv_le_inv₀ hx.1 hpos]
              -- Square both sides of the goal and get
              -- 4 * x^3 ≤ x^2.
              rw [← sq_le_sq₀ (le_of_lt hpos) (le_of_lt hx.1)]
              rw [mul_pow, mul_comm, ← Real.rpow_two, ← Real.rpow_mul (le_of_lt hx.1)]
              rw [show 3 / 2 * (2 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
              -- We get 0 ≤ x^2 * (1 - 4 * x).
              -- This inequality follows from 0 ≤ x^2 and 0 ≤ 1 - 4 * x for x < 1/16.
              suffices 0 ≤ x ^ 2 * (1 - 4 * x) by linear_combination this
              apply mul_nonneg (by positivity) (by linarith)
            · simp only [mem_Ioc]
              exact ⟨hx1, hx2⟩
            · simp only [mem_Ioc]
              norm_num
            · exact hx2
  -- Show that log(cos(x)) is integrable on [0, π / 2]
  have hint_cos : IntervalIntegrable (fun x => log (cos x)) MeasureTheory.volume 0 (π / 2) := by
    -- We have cos(x) = sin(π / 2 - x).
    simp_rw [← sin_pi_div_two_sub]
    -- So log(cos(x)) = log(sin(π / 2 - x)) is integrable because log(sin(x)) is integrable.
    have := IntervalIntegrable.comp_sub_left hint_sin (π / 2)
    simp at this
    symm
    exact this
  -- Show that log(sin(x)) is integrable on [π / 2, π].
  have hint_sin' : IntervalIntegrable (fun x => log (sin x)) MeasureTheory.volume (π / 2) π := by
    -- We have that log(sin(π - x)) is integrable on [π / 2, π].
    have := IntervalIntegrable.comp_sub_left hint_sin π
    -- sin(π - x) = sin(x) so log(sin(x)) is integrable on [π / 2, π].
    simp [show π - π / 2 = π / 2 by ring] at this
    symm
    exact this
  -- Show that log(sin(2x)) is integrable on [0, π / 2].
  have hint_2sin : IntervalIntegrable (fun x => log (sin (2 * x))) MeasureTheory.volume 0 (π / 2) := by
    rw [show (0 : ℝ) = 0 / 2 by norm_num]
    -- Integrability of log(sin(2x)) on [0, π / 2] is equivalent to integrability of
    -- log(sin(x)) on [0, π].
    rw [IntervalIntegrable.comp_mul_left_iff (f := fun x => log (sin x)) (by norm_num)]
    -- It is enough to show that log(sin(x)) is integrable on [0, π / 2] and on [π / 2, π].
    trans π / 2
    · exact hint_sin
    · exact hint_sin'
  -- Prove that ∫ x in (0)..(π/2), log (sin x) = ∫ x in (0)..(π/2), log (cos x).
  have eq1 : ∫ x in (0)..(π/2), log (sin x) = ∫ x in (0)..(π/2), log (cos x) := by
    -- We have cos(x) = sin(π / 2 - x) so
    -- ∫ x in (0)..(π/2), log (cos x) = ∫ x in (π / 2 - π / 2)..(π / 2 - 0), log (sin x).
    simp_rw [← sin_pi_div_two_sub]
    rw [intervalIntegral.integral_comp_sub_left (fun x => log (sin x))]
    simp only [sub_self, sub_zero]
  -- Prove that 2 * ∫ x in (0)..(π/2), log (sin x) = ∫ x in (0)..(π/2), log (sin (2 * x) / 2).
  have eq2 : 2 * ∫ x in (0)..(π/2), log (sin x) = ∫ x in (0)..(π/2), log (sin (2 * x) / 2) := by
    -- We have 2 * ∫ x in (0)..(π/2), log (sin x)
    --     = ∫ x in (0)..(π/2), log (sin x) + ∫ x in (0)..(π/2), log (sin x)
    --     = ∫ x in (0)..(π/2), log (sin x) + ∫ x in (0)..(π/2), log (cos x)
    --     = ∫ x in (0)..(π/2), log (sin x) + log (cos x).
    nth_rw 1 [two_mul, eq1, ← intervalIntegral.integral_add hint_cos hint_sin]
    -- It is left to prove that log(sin(x)) + log(cos(x)) = log(sin(2 * x) / 2) a.e. on [0, π / 2].
    apply intervalIntegral.integral_congr_ae
    rw [eqI (by linarith [pi_pos])]
    -- It is sufficient to show that log(sin(x)) + log(cos(x)) = log(sin(2 * x) / 2)
    -- for x ∈ (0, π / 2).
    refine ae_of_mem_of_ae_of_mem_inter_Ioo ?_
    simp only [mem_Ioc, mem_inter_iff, mem_Ioo, and_imp]
    intro a b ha1 ha2 hb1 hb2 hab
    refine MeasureTheory.ae_of_all MeasureTheory.volume ?_
    intro x hx1 _ _ hx2
    -- We have log(sin(2 * x) / 2) = log(2 * sin(x) * cos(x) / 2) = log(sin(x)) + log(cos(x)).
    -- The last equality holds because sin(x) ≠ 0 and cos(x) ≠ 0 for x ∈ (0, π / 2).
    rw [← log_mul, sin_two_mul]; ring_nf
    · apply ne_of_gt
      apply cos_pos_of_mem_Ioo
      simp only [mem_Ioo]
      constructor <;> linarith
    · apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- Prove that
  -- ∫ x in (0)..(π/2), log (sin (2 * x) / 2) = (∫ x in (0)..(π / 2), log (sin (2 * x))) - π / 2 * log 2.
  have eq3 : ∫ x in (0)..(π/2), log (sin (2 * x) / 2) = (∫ x in (0)..(π / 2), log (sin (2 * x))) - π / 2 * log 2 := by
    -- We have (∫ x in (0)..(π / 2), log (sin (2 * x))) - π / 2 * log 2
    --       = (∫ x in (0)..(π / 2), log (sin (2 * x))) - ∫ x in (0)..(π / 2), log 2
    --       = ∫ x in (0)..(π / 2), log (sin (2 * x)) - log 2.
    rw [show π / 2 * log 2 = ∫ x in (0)..(π / 2), log 2 by simp]
    rw [← intervalIntegral.integral_sub hint_2sin (by simp)]
    -- Show that log(sin(2 * x) / 2) = log (sin (2 * x)) - log 2 a.e. on [0, π / 2].
    apply intervalIntegral.integral_congr_ae
    rw [eqI (by linarith [pi_pos])]
    -- It is sufficient to show that log(sin(2 * x) / 2) = log (sin (2 * x)) - log 2
    -- for x ∈ (0, π / 2).
    refine ae_of_mem_of_ae_of_mem_inter_Ioo ?_
    simp only [mem_Ioc, mem_inter_iff, mem_Ioo, and_imp]
    intro a b ha1 ha2 hb1 hb2 hab
    refine MeasureTheory.ae_of_all MeasureTheory.volume ?_
    intro x hx1 _ _ hx2
    -- log(sin(2 * x) / 2) = log(sin(2 * x)) - log(2) because sin(2 * x) ≠ 0 for x ∈ (0, π / 2).
    rw [log_div _ (by norm_num)]
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- Prove that ∫ x in (0)..(π / 2), log (sin (2 * x)) = ∫ x in (0)..(π / 2), log (sin x).
  have eq4 : ∫ x in (0)..(π / 2), log (sin (2 * x)) = ∫ x in (0)..(π / 2), log (sin x) := calc
    ∫ x in (0)..(π / 2), log (sin (2 * x)) = (1 / 2) * (2 * ∫ x in (0)..(π / 2), log (sin (2 * x))) := by ring
    -- We have ∫ x in (0)..(π / 2), log (sin (2 * x)) = (1 / 2) * ∫ x in (0)..(π), log (sin x).
    _ = (1 / 2) * ∫ x in (0)..(π), log (sin x) := by
        rw [intervalIntegral.mul_integral_comp_mul_left (f := fun x => log (sin x))]
        ring_nf
    _ = ∫ x in (0)..(π / 2), log (sin x) := by
        -- Split the interval [0, π] into [0, π / 2] ∪ [π / 2, π] and show that
        -- ∫ x in (π / 2)..(π), log (sin x) = ∫ x in (0)..(π / 2), log (sin x).
        rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2) hint_sin hint_sin']
        have := intervalIntegral.integral_comp_sub_left (fun x => log (sin x)) π (a := π / 2) (b := π)
        -- The result follows from sin(π - x) = sin x.
        simp_rw [sin_pi_sub] at this
        rw [this, sub_self, show π - π / 2 = π / 2 by ring]
        linarith
  -- The final result can be proven automatically:
  -- 2 * ∫ x in (0)..(π / 2), log (sin x)
  -- = ∫ x in (0)..(π / 2), log (sin (2 * x) / 2) (from eq2)
  -- = (∫ x in (0)..(π / 2), log (sin (2 * x)) - π / 2 * log 2 (from eq3)
  -- = (∫ x in (0)..(π / 2), log (sin x)) - π / 2 * log 2. (from eq4)
  -- We get that
  -- ∫ x in (0)..(π / 2), log (sin x) = -π / 2 * log 2.
  linarith