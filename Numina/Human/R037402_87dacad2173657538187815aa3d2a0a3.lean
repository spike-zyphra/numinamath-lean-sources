import Mathlib

open Real intervalIntegral Polynomial 

open scoped Interval

/-Compute
$$
\int_{1}^{2} \frac{9 x+4}{x^{5}+3 x^{2}+x} d x
$$
(No, your TI-89 doesn't know how to do this one. Yes, the end is near.) -/
theorem calculus_608219 : 
    ∫ (x : ℝ) in (1 : ℝ)..2, (fun x ↦ (9 * x + 4) / (x ^ 5 + 3 * x ^ 2 + x)) x = 
    log (80 / 23) := by
  let f : ℝ → ℝ := fun x ↦ 5 * (x ^ 4 + 3 * x + 1) / (x ^ 5 + 3 * x ^ 2 + x)
  let g : ℝ → ℝ := fun x ↦ - (5 * x ^ 4 + 6 * x + 1) / (x ^ 5 + 3 * x ^ 2 + x)
  let F : ℝ → ℝ := fun x ↦ 5 * log x
  let G : ℝ → ℝ := fun x ↦ - log (x ^ 5 + 3 * x ^ 2 + x)
  let h : ℝ → ℝ := fun x ↦ eval x (X ^ 5 + 3 * X ^ 2 + X) 
  have hG : G = fun x ↦ - 1 * (log ∘ h) x := by 
    ext x 
    simp [h, G]  
  have dh : deriv h = fun x ↦ (5 * x ^ 4 + 6 * x + 1) := by 
    unfold h 
    ext x 
    rw [Polynomial.deriv] 
    simp [h]
    ring 
  have hx1 : ∀ (x : ℝ), x ∈ [[(1 : ℝ), 2]] → x > 0 := by
    intro x hx
    simp only [Nat.one_le_ofNat, Set.uIcc_of_le, Set.mem_Icc] at hx
    linarith only [hx]
  have hx2 : ∀ (x : ℝ), x ∈ [[(1 : ℝ), 2]] → (x ^ 5 + 3 * x ^ 2 + x) ≠ 0 := by
    intro x hx
    have := hx1 x hx 
    simp only [Nat.one_le_ofNat, Set.uIcc_of_le, Set.mem_Icc] at hx
    have gt1 : x ^ 5 > 0 := by 
      apply pow_pos this 
    have gt2 : 3 * x ^ 2 > 0 := by 
      apply mul_pos (by norm_num)
      exact pow_pos this 2 
    linarith only [gt1, gt2, this] 
  have cts1 : ContinuousOn (fun (x : ℝ) ↦ x ^ 5 + 3 * x ^ 2 + x) [[1, 2]] := by 
    convert_to ContinuousOn h [[1, 2]]
    · simp [h] 
    · unfold h 
      exact Polynomial.continuousOn_aeval (X ^ 5 + 3 * X ^ 2 + X) 
  have cts2 : ContinuousOn (fun (x : ℝ) ↦ 5 * (x ^ 4 + 3 * x + 1)) [[1, 2]] := by 
    convert_to ContinuousOn (fun (x : ℝ) ↦ eval x (5 * (X ^ 4 + 3 * X + 1))) _ 
    · simp 
    · exact Polynomial.continuousOn_aeval (5 * (X ^ 4 + 3 * X + 1)) 
  have cts3 : ContinuousOn (fun (x : ℝ) ↦ - (5 * x ^ 4 + 6 * x + 1) ) [[1, 2]] := by 
    convert_to ContinuousOn (fun (x : ℝ) ↦ eval x (- (5 * X ^ 4 + 6 * X + 1))) _ 
    · simp 
    · exact Polynomial.continuousOn_aeval (- (5 * X ^ 4 + 6 * X + 1)) 
  have fcts : ContinuousOn f [[1, 2]] := by 
    unfold f 
    exact ContinuousOn.div cts2 cts1 hx2 
  have gcts : ContinuousOn g [[1, 2]] := by 
    unfold g 
    exact ContinuousOn.div cts3 cts1 hx2 
  have hF : ∀ x ∈ [[1, 2]], DifferentiableAt ℝ F x := by
    intro x hx
    simp only [differentiableAt_const, F] 
    apply DifferentiableAt.const_mul 
    simp only [differentiableAt_log_iff]
    exact (hx1 x hx).ne.symm   
  have hF1 : IntervalIntegrable (deriv F) MeasureTheory.volume 1 2 := by simp [F]
  have hfF : (∫ (x : ℝ) in (1 : ℝ)..2, f x) = F 2 - F 1 := by
    calc
      ∫ (x : ℝ) in (1 : ℝ)..2, f x = ∫ (x : ℝ) in (1 : ℝ)..2, deriv F x := by
        apply integral_congr
        intro x hx
        have hx1 : x ≠ 0 := (hx1 x hx).ne.symm
        have hx2 : (x ^ 5 + 3 * x ^ 2 + x) ≠ 0 := (hx2 x hx)
        simp only [differentiableAt_const, deriv_const_mul_field', deriv_log', f, F]
        field_simp [hx1, hx2] ; ring
      _ = _ := intervalIntegral.integral_deriv_eq_sub hF hF1
  have hgG0 : ∀ x ∈ [[1, 2]], DifferentiableAt ℝ G x := by
    intro x hx
    simp only [hG, neg_mul, one_mul, differentiableAt_neg_iff]
    apply DifferentiableAt.comp 
    · simp [h]
      exact hx2 x hx 
    · simp [h]
  have dGg : ∀ (x : ℝ), x ∈ [[(1 : ℝ), 2]] → g x = deriv G x := by 
    intro x hx 
    rw [hG]
    simp only [neg_mul, one_mul, deriv.neg']
    rw [deriv_comp, dh]
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_ofNat, deriv_log', h, g]
    rw [← div_eq_inv_mul, neg_div]
    · simp [h]
      exact hx2 x hx
    · simp [h]
  have hf : IntervalIntegrable f MeasureTheory.volume 1 2 := by 
    apply ContinuousOn.intervalIntegrable 
    unfold f 
    exact ContinuousOn.div cts2 cts1 hx2 
  have hg : IntervalIntegrable g MeasureTheory.volume 1 2 := by 
    apply ContinuousOn.intervalIntegrable 
    unfold g 
    exact ContinuousOn.div cts3 cts1 hx2
  have hdG : IntervalIntegrable (deriv G) MeasureTheory.volume 1 2 := by 
    apply ContinuousOn.intervalIntegrable 
    rw [← continuousOn_congr dGg]
    exact gcts 
  have hgG : (∫ (x : ℝ) in (1 : ℝ)..2, g x) = G 2 - G 1 := by
    calc
      ∫ (x : ℝ) in (1 : ℝ)..2, g x = ∫ (x : ℝ) in (1 : ℝ)..2, deriv G x := integral_congr dGg 
      _ = _ := intervalIntegral.integral_deriv_eq_sub hgG0 hdG 
  clear* -dGg hgG0 dGg hfF hdG hf hg hgG 
  calc
    _ = (∫ (x : ℝ) in (1 : ℝ)..2, f x) + ∫ (x : ℝ) in (1 : ℝ)..2, g x := by
      rw [← integral_add hf hg]
      congr 1 ; ext x 
      simp only [f, g]
      linear_combination
    --We break the given integral into two pieces:
    --$$ \int_{1}^{2} \frac{9 x+4}{x^{5}+3 x^{2}+x} d x=
    -- 5 \int_{1}^{2} \frac{x^{4}+3 x+1}{x^{5}+3 x^{2}+x} d x-
    -- \int_{1}^{2} \frac{5 x^{4}+6 x+1}{x^{5}+3 x^{2}+x} d x$$
    _ = (F 2 - F 1) + (G 2 - G 1) := by rw [hfF, hgG] -- 
    -- These two new integrals are easily computed; for, 
    -- the first integrand reduces to $1 / x$ and the second is of the form $f^{\prime}(x) / f(x)$. 
    -- We obtain
    -- $$\left[5 \ln |x|-\ln \left|x^{5}+3 x^{2}+x\right|\right]_{1}^{2}=\ln 32-\ln 46+\ln 5
    -- =\ln \frac{80}{23}$$
    _ = _ := by
      simp only [log_one, mul_zero, sub_zero, one_pow, mul_one, sub_neg_eq_add, F, G]
      rw [← log_rpow]
      ring_nf
      rw [← log_div, ← log_mul]
      all_goals norm_num
