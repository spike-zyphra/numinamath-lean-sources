import Mathlib

namespace calculus_608392

noncomputable def f (x : ℝ) : ℝ := ∑' (n : ℕ), x ^ n / 2 ^ n

/- Observe that $f(x)$ is merely an infinite geometric series. Thus $f(x)=\frac{1}{1-\frac{x}{2}}=\frac{2}{2-x}$. -/
lemma f_eq (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) : f x = (1 - x / 2)⁻¹ := by
  unfold f
  conv =>
    enter [1, 1, n]
    rw [← div_pow]
  rw [tsum_geometric_of_abs_lt_one]
  rw [abs_lt]
  rw [lt_div_iff₀' (by norm_num), div_lt_iff₀' (by norm_num)]
  constructor <;> linarith

end calculus_608392

open Real Polynomial intervalIntegral calculus_608392

open scoped Interval

/-Let $f(x)=1+\frac{x}{2}+\frac{x^{2}}{4}+\frac{x^{3}}{8}+\ldots$, for $-1 \leq x \leq 1$.
Find $\sqrt{e^{\int_{0}^{1} f(x) d x}}$.-/
theorem calculus_608392 : √(exp (∫ (x : ℝ) in (0 : ℝ)..1, f x)) = 2 := by
  have h1 : ∫ (x : ℝ) in (0 : ℝ)..1, f x = 2 * log 2 := by -- Then $\int_{0}^{1} \frac{2}{2-x}=2 \ln 2$.
    have hx1 {x : ℝ} (hx : x ∈ [[0, 1]]) : x - 2 ≠ 0 := by
        simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hx
        linarith only [hx]
    have hd1 : Differentiable ℝ (fun x : ℝ ↦ x - 2) := by
      apply Differentiable.sub differentiable_id' (differentiable_const 2)
    have hd2 : ∀ x ∈ [[0, 1]], DifferentiableAt ℝ (fun x ↦ -2 * log (x - 2)) x := by
      intro x hx
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.log
      · simp only [differentiableAt_id', differentiableAt_const, DifferentiableAt.sub]
      · exact (hx1 hx)
    have hd3 : ∀ x ∈ [[0, 1]], (deriv fun x ↦ -2 * log (x - 2)) x = (1 - x / 2)⁻¹ := by
      intro x hx
      simp only [neg_mul, deriv.neg', differentiableAt_const, deriv_const_mul_field',
        differentiableAt_id', DifferentiableAt.sub]
      rw [deriv.log (hd1 x) (hx1 hx)]
      have hx2 : 2 - x ≠ 0 := by
        apply neg_ne_zero.1
        simp [hx1 hx]
      simp only [differentiableAt_id', differentiableAt_const, deriv_sub, deriv_id'', deriv_const',
        sub_zero, one_div]
      field_simp [hx1 hx, hx2]
      ring
    have hint: IntervalIntegrable (deriv fun x ↦ -2 * log (x - 2)) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [continuousOn_congr hd3]
      apply ContinuousOn.inv₀
      · apply Continuous.continuousOn
        convert_to Continuous (fun x : ℝ↦ eval x (1 - (C (1 / 2)) * X))
        · ext ; simp ; ring_nf
        · exact Polynomial.continuous_eval₂ (1 - C (1 / 2) * X) (RingHom.id ℝ)
      · intro x hx
        apply neg_ne_zero.1
        field_simp
        exact hx1 hx
    calc
      _ = ∫ (x : ℝ) in (0 : ℝ)..1, (1 - x / 2)⁻¹ := by
        apply integral_congr
        intro x hx
        replace hx : -1 ≤ x ∧ x ≤ 1 := by
          simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hx
          exact ⟨by linarith only [hx.1], hx.2⟩
        rw [f_eq x hx]
      _ = ∫ (x : ℝ) in (0 : ℝ)..1, deriv (fun x ↦ - 2 * log (x - 2)) x := by
        apply integral_congr
        intro x hx
        exact (hd3 x hx).symm
      _ = (fun x ↦ - 2 * log (x - 2)) 1 - (fun x ↦ - 2 * log (x - 2)) 0 :=
        intervalIntegral.integral_deriv_eq_sub hd2 hint
      _ = _ := by simp ; norm_num
  -- Then $\sqrt{e^{2 \ln 2}}=\sqrt{2^{2}}=2$.
  rw [h1]
  rw [mul_comm, exp_mul, exp_log (by norm_num)]
  rw [rpow_two]
  rw [sqrt_sq (by norm_num)]
