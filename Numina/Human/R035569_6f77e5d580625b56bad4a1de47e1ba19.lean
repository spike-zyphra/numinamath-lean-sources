import Mathlib
open Real

/- Given the function $f(x) = 2\tan(\omega x + \phi)$ where $\omega > 0$ and $|\phi| < \frac{\pi}{2}$, the smallest positive period of the function is $\frac{\pi}{2}$, and $f\left( \frac{\pi}{2} \right) = -2$, then $\omega = \_\_\_\_\_\_$, $\phi = \_\_\_\_\_\_$. -/
theorem algebra_9231 {ω φ : ℝ} (hω : ω > 0) (hφ : |φ| < π / 2)
    (f : ℝ → ℝ) (hf : f = fun x => 2 * tan (ω * x + φ))
    (hper : IsLeast {T : ℝ | T > 0 ∧ ∀ x : ℝ, f (x + T) = f x} (π / 2))
    (h2 : f (π / 2) = -2) :
    ω = 2 ∧ φ = -π / 4 := by
  -- We prove that f has fundamental period π/ω
  have hper' : IsLeast {T : ℝ | T > 0 ∧ ∀ x : ℝ, f (x + T) = f x} (π / ω) := by
    -- We need to prove that:
    -- 1. π / ω is a period of f
    -- 2. If T > 0 is a period of f, then T ≥ π / ω
    simp [hf]
    constructor
    . -- Prove that π / ω is a period of f
      refine ⟨by positivity, fun x ↦ ?_⟩
      -- f(x + π / ω) = f(x) because tan has period π
      rw [show ω * (x + π / ω) + φ = ω * x + φ + π by field_simp; ring]
      exact tan_periodic _
    . -- Prove that if T > 0 is a period of f, then T ≥ π / ω
      intro T ⟨Tpos, h⟩
      -- Suppose T < π / ω, we will derive a contradiction
      by_contra! hT
      rw [lt_div_iff' hω] at hT
      -- tan is injective on (-π/2, π/2)
      -- Let ω * x + φ < ω * (x + T) + φ ∈ (-π/2, π/2)
      -- It can be done by setting x = (- ω * T / 2 - φ) / ω
      specialize h ((- ω * T / 2 - φ) / ω)
      -- x₁ < π / 2
      have h1 : ω * ((-ω * T / 2 - φ) / ω + T) + φ < π / 2 := by
        rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hω)]
        linarith
      -- x₂ > -π / 2
      have h2 : -(π / 2) < ω * ((-ω * T / 2 - φ) / ω) + φ := by
        apply ne_of_gt at hω
        rw [mul_div_cancel₀ _ hω]
        linarith
      -- x₁ > x₂
      have h3 : ω * ((-ω * T / 2 - φ) / ω) + φ < ω * ((-ω * T / 2 - φ) / ω + T) + φ := by
        rw [← sub_lt_zero]
        ring_nf
        nlinarith
      -- x₁ = x₂ by injectivity of tan on (-π/2, π/2), which is a contradiction
      apply Real.injOn_tan at h
      . linarith
      . constructor <;> linarith
      . constructor <;> linarith

  -- f has fundamental period π/ω and fundamental period π/2, so π / ω = π / 2 and ω = 2
  have ωval := IsLeast.unique hper hper'
  field_simp at ωval
  simp [show π ≠ 0 from pi_ne_zero] at ωval
  subst ω

  -- We prove that φ = -π / 4
  refine ⟨rfl, ?_⟩
  -- Rewrite f(π / 2) = -2 as tan φ = tan (-π / 4)
  replace h2 : tan φ = tan (-π / 4) := by
    simp [show -π / 4 = -(π / 4) by ring]
    simp [hf] at h2
    rw [mul_div_cancel₀ _ (by norm_num), add_comm, tan_periodic] at h2
    linarith
  -- Use injectivity of tan on (-π/2, π/2)
  exact injOn_tan (abs_lt.1 hφ) (by constructor <;> linarith [pi_pos]) h2
