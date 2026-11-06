import Mathlib

open Real MeasureTheory

/- Example 15 Let $f(x), g(x)$ be continuous on $[a, b]$, and satisfy

$$

\int_{0}^{1} f(t) \mathrm{d} t \geqslant \int_{0}^{1} g(t) \mathrm{d} t, x \in[a, b), \int_{0}^{h} f(t) \mathrm{d} t=\int_{a}^{b} g(t) \mathrm{d} t .

$$


Prove: $\int_{a}^{b} x f(x) \mathrm{d} x \leqslant \int_{a}^{b} x g(x) \mathrm{d} x$. -/
theorem calculus_135033 {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hg : ContinuousOn g (Set.Icc a b))
    (hfg : ∀ x ∈ Set.Ico a b, ∫ t in (a)..x, f t ≥ ∫ t in (a)..x, g t)
    (hfg' : ∫ t in (a)..b, f t = ∫ t in (a)..b, g t) :
    ∫ x in (a)..b, x * f x ≤ ∫ x in (a)..b, x * g x := by
  -- Define F(x) = f(x) - g(x) and G(x) = ∫ t in a..x, F(t).
  set F : ℝ → ℝ := f - g
  set G : ℝ → ℝ := fun x => ∫ t in (a)..x, F t
  -- F(x) is continuous on [a, b].
  have hF : ContinuousOn F (Set.Icc a b) := by apply ContinuousOn.sub hf hg
  -- f is integrable on [a, x] for all x ∈ [a, b].
  have hf_int {x} (hx : x ∈ Set.Icc a b) : IntervalIntegrable f volume a x := by
    apply ContinuousOn.intervalIntegrable
    simp only [Set.mem_Icc] at hx
    simp [hx.1]
    apply ContinuousOn.mono hf
    apply Set.Icc_subset_Icc_right hx.2
  -- g is integrable on [a, x] for all x ∈ [a, b].
  have hg_int {x} (hx : x ∈ Set.Icc a b) : IntervalIntegrable g volume a x := by
    apply ContinuousOn.intervalIntegrable
    simp only [Set.mem_Icc] at hx
    simp [hx.1]
    apply ContinuousOn.mono hg
    apply Set.Icc_subset_Icc_right hx.2
  -- G(a) = 0.
  have hGa : G a = 0 := by simp [G]
  -- G(b) = ∫ t in a..b, F(t) = ∫ t in a..b, f(t) - g(t) = 0
  -- (because ∫ t in (a)..b, f t = ∫ t in (a)..b, g t).
  have hGb : G b = 0 := by
    simp [G, F]
    rw [intervalIntegral.integral_sub (hf_int (by simp [hab])) (hg_int (by simp [hab]))]
    simp only [hfg', sub_self]
  -- Show that 0 ≤ ∫ x in (a)..b, G x.
  have hG0 : 0 ≤ ∫ x in (a)..b, G x := by
    -- It is enough to show that 0 ≤ G(x) for all x ∈ [a, b].
    apply intervalIntegral.integral_nonneg hab
    simp only [Set.mem_Icc, Pi.sub_apply, and_imp, G, F]
    intro x hx1 hx2
    rw [intervalIntegral.integral_sub (hf_int (by simp [hx1, hx2])) (hg_int (by simp [hx1, hx2]))]
    -- Consider two cases: x < b or x = b.
    by_cases h : x < b
    · -- If x < b then the result follows from
      -- ∫ t in (a)..x, f t ≥ ∫ t in (a)..x, g t)
      -- for all x ∈ [a, b).
      have := hfg x (by simp [hx1, h])
      linarith
    -- If x = b then G(b) = 0 ≥ 0.
    rw [show x = b by linarith, hfg', sub_self]
  -- Show that G'(x) = F(x) for all x ∈ (a, b).
  have hdG {x} (hx : x ∈ Set.Ioo a b) : HasDerivAt G (F x) x := by
    have hx' : x ∈ Set.Icc a b := Set.mem_Icc_of_Ioo hx
    -- We have G(x) = ∫ t in a..x, F(t), so G'(x) = F(x)
    -- when the following conditions are satisfied.
    apply intervalIntegral.integral_hasDerivAt_right
    · -- F is integrable on [a, x].
      apply IntervalIntegrable.sub (hf_int hx') (hg_int hx')
    · -- F is strongly measurable in a neighborhood of x because
      -- F is continuous on (a, b).
      apply ContinuousOn.stronglyMeasurableAtFilter (s := Set.Ioo a b) isOpen_Ioo _ _ hx
      apply hF.mono
      exact Set.Ioo_subset_Icc_self
    · -- F is continuous at x ∈ (a, b).
      apply hF.continuousAt
      exact Icc_mem_nhds_iff.mpr hx
  -- ∫ x in (a)..b, x * f x ≤ ∫ x in (a)..b, x * g x
  -- is equivalent to
  -- ∫ x in (a)..b, x * f x - x * g x ≤ 0.
  rw [← sub_nonpos, ← intervalIntegral.integral_sub]
  rotate_left
  · -- Show that x * f x is integrable on [a, b].
    apply IntervalIntegrable.mul_continuousOn
    · apply Continuous.intervalIntegrable (by fun_prop)
    · simp [hab, hf]
  · -- Show that x * g x is integrable on [a, b].
    apply IntervalIntegrable.mul_continuousOn
    · apply Continuous.intervalIntegrable (by fun_prop)
    · simp [hab, hg]
  calc
    -- We have
    -- ∫ x in (a)..b, x * f x - x * g x
    --    = ∫ x in (a)..b, x * F x
    --    = b * G b - a * G a - ∫ x in (a)..b, G x
    -- (from the integration by parts formula)
    --    = 0 - 0 - ∫ x in (a)..b, G x
    --    = -∫ x in (a)..b, G x
    --    ≤ 0
    -- (from hG0).
    ∫ x in (a)..b, x * f x - x * g x = ∫ x in (a)..b, x * F x := by
      apply intervalIntegral.integral_congr
      intro x
      simp [F, mul_sub]
    _ = b * G b - a * G a - ∫ x in (a)..b, G x := by
      -- Apply the integration by parts formula to ∫ x in (a)..b, x * F x.
      rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right (v := G) (u' := 1)]
      · simp
      · -- x is continuous on [a, b].
        fun_prop
      · -- Show that G is continuous on [a, b].
        -- It is enough to show that F is integrable on [a, b].
        apply intervalIntegral.continuousOn_primitive_interval
        simp [hab]
        apply ContinuousOn.integrableOn_Icc hF
      · -- The derivative of x is 1.
        intro x hx
        simp
        apply HasDerivAt.hasDerivWithinAt
        exact hasDerivAt_id' x
      · -- The derivative of G(x) is F(x) for x ∈ (a, b).
        simp only [min_eq_left, hab, max_eq_right]
        intro x hx
        apply HasDerivAt.hasDerivWithinAt
        apply hdG hx
      · apply intervalIntegrable_const
      · apply ContinuousOn.intervalIntegrable
        simpa only [hab, Set.uIcc_of_le]
    _ ≤ 0 := by
      simp [hGa, hGb, hG0]