import Mathlib

open Real intervalIntegral

open scoped Interval

/-Let $f: \mathbf{R} \rightarrow \mathbf{R}$ be a continuous function with
$\int_{0}^{1} f(x) f^{\prime}(x) d x=0$
and $\int_{0}^{1} f(x)^{2} f^{\prime}(x) d x=$ 18.
What is $\int_{0}^{1} f(x)^{4} f^{\prime}(x) d x$ ?-/
theorem calculus_611315 (f : ℝ → ℝ) (hf : Differentiable ℝ f )
    (hf' : ContinuousOn (deriv f) [[0, 1]])
    (h1 : ∫ (x : ℝ) in (0 : ℝ)..1, f x * deriv f x = 0)
    (h2 : ∫ (x : ℝ) in (0 : ℝ)..1, (f x) ^ 2 * deriv f x = 18) :
    ∫ (x : ℝ) in (0 : ℝ)..1, (f x) ^ 4 * deriv f x = 486 / 5 := by
  have h : ∀ x ∈ [[0, 1]], HasDerivAt f (deriv f x) x := by
    intro x hx
    simp only [hasDerivAt_deriv_iff]
    exact hf x
  replace h1 : 0 = 1 / 2 * ((f 1) ^ 2 - (f 0) ^ 2) := by
    calc
      _ = ∫ (x : ℝ) in (0 : ℝ)..1, ((fun x ↦ x) ∘ f) x * deriv f x := by simp [h1]
      -- 0=\int_{0}^{1} f(x) f^{\prime}(x) d x
      _ = ∫ (u : ℝ) in (f 0)..(f 1), (fun x ↦ x) u :=
        integral_comp_mul_deriv h hf' continuous_id'
      -- =\int_{f(0)}^{f(1)} u d u
      _ = 1 / 2 * ((f 1) ^ 2 - (f 0) ^ 2) := by
        simp only [integral_id]
        ring
      -- =\frac{1}{2}\left(f(1)^{2}-f(0)^{2}\right)
  replace h2 : 18 = 1 / 3 * ((f 1) ^ 3 - (f 0) ^ 3) := by
    calc
      _ = ∫ (x : ℝ) in (0 : ℝ)..1, ((fun x ↦ x ^ 2) ∘ f) x * deriv f x := by simp [h2]
      -- 18=\int_{0}^{1} f(x)^{2} f^{\prime}(x) d x
      _ = ∫ (u : ℝ) in (f 0)..(f 1), (fun x ↦ x ^ 2) u :=
        integral_comp_mul_deriv h hf' (continuous_pow 2)
      -- = \int_{f(0)}^{f(1)} u^{2} d u
      _ = 1 / 3 * ((f 1) ^ 3 - (f 0) ^ 3) := by
        simp only [integral_pow, Nat.reduceAdd, Nat.cast_ofNat, one_div]
        ring
      -- =\frac{1}{3}\left(f(1)^{3}-f(0)^{3}\right)
  simp only [one_div, zero_eq_mul, inv_eq_zero, OfNat.ofNat_ne_zero, false_or, sub_eq_zero] at h1
  rw [sq_eq_sq_iff_eq_or_eq_neg] at h1
  -- The first equation implies $f(0)= \pm f(1)$.
  rcases h1 with (h1 | h1)
  · absurd h2
    -- The second equation shows that $f(0) \neq f(1)$
    rw [h1]
    norm_num
  · rw [h1] at h2
    ring_nf at h2
    replace h2 : (f 0) ^ 3 = (- 3) ^ 3 := by
      calc
        _ = f 0 ^ 3 * (-2 / 3) * (- 3 / 2) := by ring
        _ = _ := by rw [← h2] ; norm_num
    rw [pow_eq_pow_iff_of_ne_zero (by norm_num)] at h2
    simp only [neg_neg, show ¬Even 3 by decide, and_false, or_false] at h2
    rw [h2, neg_neg] at h1
    -- and in fact $54=f(1)^{3}-f(0)^{3}=2 f(1)^{3}$, so $f(1)=3$ and $f(0)=-3$
    calc
      _ = ∫ (x : ℝ) in (0 : ℝ)..1, ((fun x ↦ x ^ 4) ∘ f) x * deriv f x := by
        simp only [Function.comp_apply]
      _ = ∫ (u : ℝ) in (f 0)..(f 1), (fun x ↦ x ^ 4) u :=
        integral_comp_mul_deriv h hf' (continuous_pow 4)
      -- \int_{0}^{1} f(x)^{4} f^{\prime}(x) d x=\int_{f(0)}^{f(1)} u^{4} d u
      _ = (f 1 ^ 5 - f 0 ^ 5) / 5 := by
        simp only [integral_pow, Nat.reduceAdd, Nat.cast_ofNat] ; ring 
      -- =\frac{1}{5}\left(f(1)^{5}-f(0)^{5}\right)
      _ = _ := by -- =\frac{1}{5}(243+243)=\frac{486}{5}
        rw [h1, h2]
        norm_num
      
