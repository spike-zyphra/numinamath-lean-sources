import Mathlib

open Real

/- 4. The function $f:[a, b] \rightarrow \mathbb{R}$ is differentiable, with $0 \leq f^{\prime}(x) \leq 1, \forall x \in[a, b]$ and $f(a)=0$.

Show that $3\left(\int_{a}^{b} f^{2}(x) d x\right)^{3} \geq \int_{a}^{b} f^{8}(x) d x$.

Ion Bursuc -/
theorem calculus_110647 {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Set.Icc a b)) (h : ∀ x ∈ Set.Icc a b, 0 ≤ deriv f x ∧ deriv f x ≤ 1)
    (h0 : f a = 0) :
    3 * (∫ x in a..b, (f x)^2)^3 ≥ ∫ x in a..b, (f x)^8 := by
  -- f(x) is differentiable on [a, b] so f(x) ^ n is continuous on [a, t] for all t ≤ b.
  have hfn n {t} (ht : t ≤ b) : ContinuousOn (fun x => f x ^ n) (Set.Icc a t) := by
    apply ContinuousOn.pow (hf.continuousOn.mono _)
    exact Set.Icc_subset_Icc_right ht
  -- f(x) ^ n is continuous on [a, t] for all t ∈ [a, b], so f(x) ^ n is integrable on [a, t].
  have hfn_int {n t} (hta : a ≤ t) (htb : t ≤ b) : IntervalIntegrable (fun x ↦ f x ^ n) MeasureTheory.volume a t := by
    apply ContinuousOn.intervalIntegrable_of_Icc hta
    exact hfn n htb
  -- f(x) is differentiable on [a, b] so f(x) has a derivative at all points in (a, t) for t ≤ b.
  have hderiv {t} (ht : t ≤ b) : ∀ x ∈ Set.Ioo a t, HasDerivAt f (deriv f x) x := by
      simp only [Set.mem_Ioo, and_imp]
      intro x hax hxt
      apply hf.hasDerivAt
      simp only [Icc_mem_nhds_iff, Set.mem_Ioo]
      exact ⟨hax, by linarith⟩
  -- Show that the derivative of f(x) is integrable on [a, t] for t ∈ [a, b].
  have hdf_int {t} (hat : a ≤ t) (htb : t ≤ b) : IntervalIntegrable (deriv f) MeasureTheory.volume a t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hat]
    -- It is enough to show that the derivative is nonnegative.
    apply intervalIntegral.integrableOn_deriv_of_nonneg _ (hderiv htb)
    · simp only [Set.mem_Ioo, and_imp]
      intro t hat htx
      apply (h t _).1
      simp only [Set.mem_Icc]
      constructor <;> linarith
    · apply hf.continuousOn.mono
      exact Set.Icc_subset_Icc_right htb
  -- Let g(t) = 3 * (∫ x in a..t, (f x)^2)^3 - ∫ x in a..t, (f x)^8
  set g : ℝ → ℝ := fun t => 3 * (∫ x in a..t, (f x)^2)^3 - ∫ x in a..t, (f x)^8
  -- Let g'(t) = (f t)^2  * (9 * (∫ x in a..t, (f x)^2)^2 - (f t)^6)
  set g' : ℝ → ℝ := fun t => (f t)^2  * (9 * (∫ x in a..t, (f x)^2)^2 - (f t)^6)
  rw [ge_iff_le, ← sub_nonneg]
  rw [← show g a = 0 by simp [g]]
  -- The goal can be changed to g(a) ≤ g(b) (because g(a) = 0).
  change g a ≤ g b
  -- Show that the derivative of g(t) is g'(t) for all t ∈ (a, b).
  have hgd {t} (ht : t ∈ Set.Ioo a b): HasDerivAt g (g' t) t := by
    simp only [Set.mem_Ioo] at ht
    -- Show that the derivative of v_n(t) = ∫ x in a..t, (f x)^n) is f(t) ^ n.
    have hd_int {n} : HasDerivAt (fun t => ∫ x in a..t, (f x)^n) (f t ^ n) t := by
      apply intervalIntegral.integral_hasDerivAt_right
      · exact hfn_int (le_of_lt ht.1) (le_of_lt ht.2)
      · apply ContinuousOn.stronglyMeasurableAtFilter (s := Set.Ioo a b) isOpen_Ioo
        · apply (hfn n (le_refl b)).mono
          exact Set.Ioo_subset_Icc_self
        · simp only [Set.mem_Ioo, ht, and_self]
      · apply (hfn n (le_refl b)).continuousAt
        simp only [Icc_mem_nhds_iff, Set.mem_Ioo, ht, and_self]
    simp [g, g', mul_sub]
    -- The result follows from basic properties of derivatives:
    -- g(t) = 3 * v_2(t)^3 - v_8(t)
    -- g'(t) = 9 * v_2(t)^2 * v_2'(t) - v_8'(t) = 9 * v_2(t)^2 * f(t)^2 - f(t)^8
    --       = f(t)^2 * (9 * v_2(t)^2 - f(t)^6).
    apply HasDerivAt.sub
    · rw [show ∀ y, (f t)^2 * (9 * y) = 3 * (3 * y * (f t)^2) by intro y; ring]
      apply HasDerivAt.const_mul
      apply HasDerivAt.pow
      exact hd_int
    · simp only [← pow_add, Nat.reduceAdd]
      exact hd_int
  -- g is differentiable on (a, b).
  have hg_diff : DifferentiableOn ℝ g (Set.Ioo a b) := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    exact (hgd hx).differentiableAt
  -- Show that g(a) ≤ g(b) by showing that 0 ≤ g'(t) for all t ∈ (a, b).
  apply monotoneOn_of_deriv_nonneg (D := Set.Icc a b) (convex_Icc a b) _ _ _ (by simp [hab]) (by simp [hab]) hab
  -- First of all, we need to prove that g is continuous on [a, b].
  · simp [g]
    -- Show that v_n(t) = ∫ x in a..t, (f x)^n is continuous on [a, b].
    have hg_int {n} : ContinuousOn (fun t => ∫ x in a..t, (f x)^n) (Set.Icc a b) := by
      have eq : Set.Icc a b = Set.uIcc a b := Eq.symm (Set.uIcc_of_le hab)
      rw [eq]
      -- Interval integrals of integrable functions are continuous.
      apply intervalIntegral.continuousOn_primitive_interval
      rw [← eq]
      apply ContinuousOn.integrableOn_Icc
      exact hfn n (le_refl b)
    apply ContinuousOn.sub (by fun_prop) (by fun_prop)
  · simp only [interior_Icc]
    exact hg_diff
  -- We need to show that 0 ≤ g'(x) for x ∈ (a, b).
  simp only [interior_Icc, Set.mem_Ioo, and_imp]
  intro x hax hxb
  suffices 0 ≤ g' x by rwa [(@hgd x (by simp; exact ⟨hax, hxb⟩)).deriv]
  dsimp [g']
  -- g'(x) = f(x)^2  * (9 * (∫ t in a..x, f(t)^2)^2 - f(x)^6)
  -- 0 ≤ f(x)^2 so it is left to show that f(x)^6 ≤ 9 * (∫ t in a..x, f(t)^2)^2.
  apply mul_nonneg (by positivity)
  simp only [sub_nonneg]
  -- Prove that f(x)^2 * f'(x) is integrable on [a, t] for all t ∈ [a, b].
  have hint2 {t} (hat : a ≤ t) (htb : t ≤ b) : IntervalIntegrable (fun x ↦ f x ^ 2 * deriv f x) MeasureTheory.volume a t := by
    apply IntervalIntegrable.continuousOn_mul (hdf_int hat htb)
    rw [Set.uIcc_of_le hat]
    exact hfn 2 htb
  calc
    -- Show that f(x)^6 = (3 * ∫ t in a..x, f(t)^2 * f'(t))^2
    f x ^ 6 = (3 * ∫ t in a..x, f t ^ 2 * deriv f t) ^ 2 := by
        -- It is enough to show that f(x)^3 = ∫ t in a..x, 3 * f(t)^2 * f'(t).
        simp_rw [show f x ^ 6 = (f x ^ 3) ^ 2 by ring, ← intervalIntegral.integral_const_mul, ← mul_assoc]
        congr
        -- We have that the derivative of f(t)^3 is 3 * f(t) * f'(t) for all t ∈ (a, x).
        have hd t (ht : t ∈ Set.Ioo a x) : HasDerivAt (fun x => f x ^ 3) (3 * f t ^ 2 * deriv f t) t := by
          apply HasDerivAt.pow
          exact hderiv (le_of_lt hxb) _ ht
        -- Use the fundamental theorem of calculus to show that
        -- ∫ t in a..x, 3 * f(t)^2 * f'(t) = ∫ t in a..x, (f(t)^3)' = f(x)^3 - f(a)^3 = f(x)^3.
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hax) (hfn 3 (le_of_lt hxb)) hd, h0, zero_pow (by norm_num), sub_zero]
        simp_rw [mul_assoc]
        apply IntervalIntegrable.const_mul
        exact hint2 (le_of_lt hax) (le_of_lt hxb)
    -- Show that (3 * ∫ t in a..x, f(t)^2 * f'(t))^2 ≤ (3 * ∫ t in a..x, f(t)^2)^2
    _ ≤ (3 * ∫ t in a..x, f t ^ 2) ^ 2 := by
        rw [sq_le_sq₀]
        -- Show that ∫ t in a..x, f(t)^2 * f'(t) ≤ ∫ t in a..x, f(t)^2.
        · rw [mul_le_mul_left (by norm_num)]
          apply intervalIntegral.integral_mono_on (le_of_lt hax)
          · exact hint2 (le_of_lt hax) (le_of_lt hxb)
          · exact hfn_int (le_of_lt hax) (le_of_lt hxb)
          -- It is enough to show that f(t)^2 * f'(t) ≤ f(t)^2 for all t ∈ [a, x].
          -- This follows from the assumption that f'(t) ≤ 1 for t ∈ [a, b].
          · intro t ht
            nth_rw 2 [← mul_one (f t ^ 2)]
            gcongr
            apply (h t _).2
            simp only [Set.mem_Icc] at ht ⊢
            exact ⟨ht.1, by linarith⟩
        -- Show that ∫ t in a..x, f(t)^2 * f'(t) is nonnegative.
        -- It follows from 0 ≤ f(t)^2 * f'(t) for all t ∈ [a, b].
        · apply mul_nonneg (by norm_num)
          apply intervalIntegral.integral_nonneg (le_of_lt hax)
          intro t ht
          apply mul_nonneg (by positivity)
          apply (h t _).1
          simp only [Set.mem_Icc] at ht ⊢
          exact ⟨ht.1, by linarith⟩
        -- Show that ∫ t in a..x, f(t)^2 is nonnegative.
        -- It follows from 0 ≤ f(t)^2 for all t.
        · apply mul_nonneg (by norm_num)
          apply intervalIntegral.integral_nonneg (le_of_lt hax)
          intro t ht
          positivity
    _ = 9 * (∫ t in a..x, f t ^ 2) ^ 2 := by ring