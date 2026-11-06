import Mathlib

open Real MeasureTheory

-- The function f(x) = (a + b * x^2) / (1 + x^4) is integrable on ℝ
-- for any real constants a and b.
lemma intergrable_a_add_bx2_sub_x2_div_one_add_x4 (a  b : ℝ) :
    Integrable (fun x : ℝ => (a + b * x^2) / (1 + x^4)) volume := by
  -- Show that f is integrable on (-∞, 0] and on [0, ∞).
  rw [← integrableOn_univ, show Set.univ = Set.Iic (0 : ℝ) ∪ Set.Ici 0 by simp]
  rw [integrableOn_union]
  -- It is enough to show that f is integrable on [0, ∞).
  suffices IntegrableOn (fun x : ℝ => (a + b * x^2) / (1 + x^4)) (Set.Ici 0) volume by
    simp_rw [this, and_true]
    -- We have f(-x) = f(x).
    have eq : (fun x : ℝ => (a + b * x^2) / (1 + x^4)) ∘ Neg.neg = (fun x => (a + b * x^2) / (1 + x^4)) := by
      ext x
      simp only [one_div, Function.comp_apply, inv_inj, add_right_inj]
      ring
    -- It is enough to show that f(-x) = f(x) is integrable on -(-∞, 0] = [0, ∞).
    rw [← MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _) measurableEmbedding_neg]
    simp only [Set.neg_preimage, Set.neg_Iic, neg_zero, eq, this]
  -- We have [0, ∞) = [0, 1] ∪ [1, ∞).
  rw [show Set.Ici (0 : ℝ) = Set.Icc 0 1 ∪ Set.Ici 1 by simp]
  apply IntegrableOn.union
  · -- f is integrable on [0, 1] because f is continuous on [0, 1].
    apply Continuous.integrableOn_Icc
    apply Continuous.div (by fun_prop) (by fun_prop)
    intros; positivity
  · -- To show that f is integrable on [1, ∞),
    -- prove that |f(x)| ≤ |(|a| + |b|) * x^-2| for all x ≥ 1.
    apply MeasureTheory.Integrable.mono' (g := fun x => (|a| + |b|) * x^(-2 : ℝ)) _
    · -- Show that f(x) is measurable.
      apply AEMeasurable.aestronglyMeasurable
      apply AEMeasurable.div
      · apply AEMeasurable.const_add
        apply AEMeasurable.const_mul
        apply AEMeasurable.pow_const
        apply aemeasurable_id'
      · apply AEMeasurable.const_add
        apply AEMeasurable.pow_const
        apply aemeasurable_id'
    · -- Show that |f(x)| ≤ |(|a| + |b|) * x^-2| for all x ≥ 1.
      apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      simp only [Set.mem_Ici, norm_div, norm_eq_abs]
      intro x hx
      rw [abs_of_nonneg (a := 1 + x^4) (by positivity)]
      rw [rpow_neg (by linarith), ← one_div, mul_div, mul_one]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [show (2 : ℝ) = (2 : ℕ) by simp, rpow_natCast]
      -- We need to prove that
      -- |a + b * x^2| * x^2 ≤ (|a| + |b|) * (1 + x^4).
      calc
        -- We have
        -- |a + b * x^2| ≤ |a| + |b| * x^2.
        |a + b * x ^ 2| * x ^ 2 ≤ (|a| + |b| * x^2) * x^2 := by
          gcongr
          apply le_trans (abs_add _ _)
          rw [abs_mul, abs_of_nonneg (a := x^2) (by positivity)]
        -- We have |a| ≤ |a| * x^2.
        _ ≤ (|a| * x^2 + |b| * x^2) * x^2 := by
          rw [← mul_one |a|]
          gcongr
          · linarith
          · nlinarith
        -- We get |a + b * x^2| * x^2 ≤ (|a| + |b|) * x^4
        --            ≤ (|a| + |b|) * (1 + x^4).
        _ = (|a| + |b|) * x^4 := by ring
        _ ≤ (|a| + |b|) * (1 + x^4) := by
          gcongr
          linarith
    · -- The function (|a| + |b|) * x^-2 is integrable
      -- on [1, ∞) because x^-2 is integrable on any
      -- interval [c, ∞) for c > 0.
      apply Integrable.const_mul
      rw [← IntegrableOn.eq_1]
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      rw [integrableOn_Ioi_rpow_iff] <;> norm_num

-- Show that
-- ∫ x in [0, ∞), x^2 / (1 + x^4) = ∫ x in [0, ∞), 1 / (1 + x^4).
lemma integral_one_div_one_add_x4_eq_x2_div_one_add_x4 :
    ∫ x in Set.Ici (0 : ℝ), x^2 / (1 + x^4) = ∫ x in Set.Ici (0 : ℝ), 1 / (1 + x^4) := by
  simp_rw [integral_Ici_eq_integral_Ioi]
  -- We have that
  -- ∫ x in (0, ∞), (|p| * x ^ (p - 1)) • g (x ^ p) = ∫ y in (0, ∞), g y
  -- for all p ≠ 0.
  -- Apply this theorem with p = -1.
  rw [← integral_comp_rpow_Ioi (p := -1) _ (by norm_num)]
  apply setIntegral_congr_fun (by simp)
  intro x
  -- We need to show that
  -- x^-2 * (x^-2 / (1 + x^-4)) = 1 / (1 + x^4) for x > 0.
  simp only [Set.mem_Ioi, abs_neg, abs_one, one_mul, smul_eq_mul, rpow_neg_one]
  intro hx
  field_simp
  ring_nf
  simp_rw [← rpow_natCast]
  simp_rw [← rpow_add hx]
  norm_num

-- Show that
-- ∫ x in [0, ∞), (1 - x^2) / (1 + x^4) = 0
lemma integral_one_sub_x2_div_one_add_x4_eq_zero :
    ∫ x in Set.Ici (0 : ℝ), (1 - x^2) / (1 + x^4) = 0 := by
  -- We have
  -- ∫ x in [0, ∞), (1 - x^2) / (1 + x^4)
  --   = ∫ x in [0, ∞), 1 / (1 + x^4) - ∫ x in [0, ∞), x^2 / (1 + x^4)
  --   = 0 (from the previous lemma).
  simp_rw [show ∀ x : ℝ, (1 - x^2) / (1 + x^4) = 1 / (1 + x^4) - x^2 / (1 + x^4) by intros; ring]
  rw [integral_sub, integral_one_div_one_add_x4_eq_x2_div_one_add_x4, sub_self]
  · -- Show that 1 / (1 + x^4) is integrable.
    -- The result follows from the fact that
    -- (a + b * x) / (1 + x^4) is integrable with a = 1 and b = 0.
    have hint := intergrable_a_add_bx2_sub_x2_div_one_add_x4 1 0
    simp_rw [zero_mul, add_zero] at hint
    exact hint.integrableOn
  · -- Show that x^2 / (1 + x^4) is integrable.
    -- The result follows from the fact that
    -- (a + b * x) / (1 + x^4) is integrable with a = 0 and b = 1.
    have hint := intergrable_a_add_bx2_sub_x2_div_one_add_x4 0 1
    simp only [one_mul, zero_add] at hint
    exact hint.integrableOn

/- 10. Evaluate
$$
\int_{-\infty}^{\infty} \frac{1-x^{2}}{1+x^{4}} d x
$$
 -/
theorem calculus_188291 : ∫ x : ℝ, (1 - x^2) / (1 + x^4) = 0 := by
  -- We have (1 - x) / (1 + x^4) is integrable.
  have hint := intergrable_a_add_bx2_sub_x2_div_one_add_x4 1 (-1)
  simp_rw [neg_one_mul, ← sub_eq_add_neg] at hint
  -- Rewrite the integral as follows:
  -- ∫ x : ℝ, (1 - x^2) / (1 + x^4)
  --    = ∫ x ≤ 0, (1 - x^2) / (1 + x^4) + ∫ 0 < x, (1 - x^2) / (1 + x^4).
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn hint.integrableOn]
  -- The second integral is equal to 0 (from integral_one_sub_x2_div_one_add_x4_eq_zero).
  rw [← integral_Ici_eq_integral_Ioi, integral_one_sub_x2_div_one_add_x4_eq_zero, add_zero]
  -- We have 0 = -0 and (-x)^4 = x^4, so the first integral can be written as
  -- ∫ x ≤ 0, (1 - x^2) / (1 + x^4)
  --     = ∫ x > 0, (1 - (-x)^2) / (1 + (-x)^4)
  --     = ∫ x ≥ 0, (1 - x^2) / (1 + x^4) = 0.
  rw [show (0 : ℝ) = -0 by norm_num, ← integral_comp_neg_Ioi]
  have eq (x : ℝ) : (-x)^4 = x^4 := by ring
  simp_rw [eq, neg_pow_two, ← integral_Ici_eq_integral_Ioi]
  rw [integral_one_sub_x2_div_one_add_x4_eq_zero, neg_zero]