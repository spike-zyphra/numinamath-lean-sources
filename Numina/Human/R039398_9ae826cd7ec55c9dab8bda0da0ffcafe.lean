import Mathlib

open Filter Real Topology Set

/- Compute:

$$
\lim _{x \rightarrow 0} \frac{x^{2}}{1-\cos (x)}
$$ -/
theorem calculus_608142 :
    Tendsto (fun (x : ℝ) => x ^ 2 / (1 - cos x)) (𝓝[≠] 0) (𝓝 2) := by
  -- Apply L'Hôpital's rule
  refine deriv.lhopital_zero_nhds' ?_ ?_ ?_ ?_ ?_
  . -- Condition 1: x ^ 2 is differentiable at a punctured neighbourhood of 0
    simp
  . -- Condition 2: (1 - cos x)' ≠ 0 on a punctured neighbourhood of 0
    -- i.e. sin x ≠ 0 on a punctured neighbourhood of 0
    simp
    -- [-π/2, π/2] \ {0} is a punctured neighbourhood of 0
    refine eventually_iff_exists_mem.mpr ⟨Icc (-π / 2) (π / 2) \ {0}, ?_, ?_⟩
    . -- Because [-π/2, π/2] is a neighbourhood of 0
      convert inter_mem_nhdsWithin _ (show Icc (-π / 2) (π / 2) ∈ 𝓝 0 from Icc_mem_nhds (by linarith [pi_pos]) (by positivity)) using 1
      ext x
      simp
      tauto
    . -- sin is strictly monotone on [-π/2, π/2]
      -- So sin x ≠ 0 on [-π/2, π/2] \ {0}
      intro x ⟨h₁, h₂⟩ h₃
      rw [show 0 = sin 0 by simp] at h₃
      apply (Real.strictMonoOn_sin).injOn at h₃
      . simp [h₃] at h₂
      . convert h₁ using 2
        ring
      . simp
        positivity
  . -- Condition 3: x ^ 2 → 0 as x →[≠] 0
    -- We use the fact that x ^ 2 is a continuous function and takes value 0 at 0
    refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    convert Continuous.tendsto (f := fun (x : ℝ) ↦ x ^ 2) (by continuity) 0
    simp
  . -- Condition 4: 1 - cos x → 0 as x →[≠] 0
    -- We use the fact that 1 - cos x is a continuous function and takes value 0 at 0
    refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    convert Continuous.tendsto (f := fun x ↦ 1 - cos x) (by continuity) 0
    simp
  simp
  -- Condition 5: 2 * x / sin x → 2 as x →[≠] 0
  -- We use L'Hôpital's rule again
  refine deriv.lhopital_zero_nhds' ?_ ?_ ?_ ?_ ?_
  . -- Condition 1: 2 * x is differentiable at a punctured neighbourhood of 0
    refine eventually_nhdsWithin_of_forall ?_
    rintro x -
    apply DifferentiableAt.mul <;> simp
  . -- Condition 2: (sin x)' ≠ 0 on a punctured neighbourhood of 0
    -- i.e. cos x ≠ 0 on a punctured neighbourhood of 0
    simp
    -- That's because cos is continuous and takes value 1 at 0
    refine Filter.Tendsto.eventually_ne (b₁ := 1) ?_ (by simp)
    refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    convert Continuous.tendsto (f := cos) (by continuity) 0
    simp
  . -- Condition 3: 2 * x → 0 as x →[≠] 0
    -- We use the fact that 2 * x is a continuous function and takes value 0 at 0
    refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    convert Continuous.tendsto (f := fun (x : ℝ) ↦ 2 * x) (by continuity) 0
    simp
  . -- Condition 4: sin x → 0 as x →[≠] 0
    -- We use the fact that sin is continuous and takes value 0 at 0
    refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    convert Continuous.tendsto (f := sin) (by continuity) 0
    simp
  . -- Condition 5: 2 / cos x → 2 as x →[≠] 0
    -- Because cos is continuous and takes value 1 at 0
    simp
    refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    convert Filter.Tendsto.div (f := fun (x : ℝ) ↦ deriv (fun x ↦ 2 * x) x) (g := cos) (l := 𝓝 0) (a := 2) (b := 1) ?_ ?_ (by simp) using 1
    . simp
    . conv =>
        arg 1
        ext x
        rw [deriv_const_mul _ (by simp)]
        simp
      simp
    . convert Continuous.tendsto (f := cos) (by continuity) 0
      simp
