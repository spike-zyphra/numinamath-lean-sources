import Mathlib

open Real

/- 1. Let $f:[0,1] \rightarrow \mathbf{R}$ be a continuous and injective function with the property that $f(1)=1$. Prove that if there exists $x_{0} \in(0,1)$ such that $f\left(x_{0}\right) \geq 2$, then $\int_{0}^{1} \operatorname{arctg}(f(x)) d x>\frac{3}{4}$. -/
theorem calculus_114864
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hinjective : Set.InjOn f (Set.Icc 0 1))
    (hf1 : f 1 = 1)
    (x0 : ℝ)
    (hx0 : x0 ∈ Set.Ioo 0 1)
    (hfx0 : f x0 ≥ 2) :
    ∫ x in (0)..1, Real.arctan (f x) > 3 / 4 := by
  -- f is continuous on [0, 1] and f is injective on [0, 1].
  -- So f is either strictly increasing or strictly decreasing on [0, 1].
  cases' hf.strictMonoOn_of_injOn_Icc' zero_le_one hinjective with h hmono
  -- Assume that f is strictly increasing.
  · simp only [StrictMonoOn, Set.mem_Icc, and_imp, Set.mem_Ioo] at h hx0
    -- We have 1 = f(1) > f (x0) ≥ 2, a contradiction.
    specialize h (le_of_lt hx0.1) (le_of_lt hx0.2) zero_le_one (le_refl 1) hx0.2
    linarith
  calc
    -- Show that ∫ x in (0)..1, arctan (f x) ≥ ∫ x in (0)..1, arctan 1.
    ∫ x in (0)..1, Real.arctan (f x) ≥ ∫ x in (0)..1, Real.arctan 1 := by
        apply intervalIntegral.integral_mono_on zero_le_one (by simp)
        -- Show that arctan (f x) is integrable on [0, 1].
        -- It is enough to show that arctan (f x) is continuous on [0, 1].
        · apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
          rw [show (fun x => arctan (f x)) = arctan ∘ f by ext x; simp]
          exact Continuous.comp_continuousOn continuous_arctan hf
        -- Now show that arctan (f x) ≥ arctan 1.
        -- The result follows from 1 = f 1 ≤ f x (because f is strictly decreasing) and x ≤ 1.
        intro x hx
        gcongr
        rw [← hf1]
        exact hmono.antitoneOn hx unitInterval.one_mem (by simp at hx; exact hx.2)
    -- ∫ x in (0)..1, arctan 1 = arctan 1 = π / 4.
    _ = π / 4 := by simp
    -- π / 4 > 3 / 4.
    _ > 3 / 4 := by linarith [Real.pi_gt_d2]