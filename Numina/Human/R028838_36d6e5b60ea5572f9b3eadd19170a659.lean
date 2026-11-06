import Mathlib

open Real

namespace inequalities_95940

variable {s : Set ℝ} {f : ℝ → ℝ}

theorem ConvexOn.map_sum_le_fin_three_real {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hf : ConvexOn ℝ s f)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s)
    (hw : w₁ + w₂ + w₃ = 1) :
    f (w₁ • p₁ + w₂ • p₂ + w₃ • p₃) ≤ w₁ • f p₁ + w₂ • f p₂ + w₃ • f p₃ := by
  have h₀ : (∀ i ∈ Finset.univ, 0 ≤ ![w₁, w₂, w₃] i) := by
    intro i
    fin_cases i
    all_goals simpa
  have h₁ : (∑ i ∈ Finset.univ, ![w₁, w₂, w₃] i = 1) := by
    simp [Fin.sum_univ_three, hw]
  have hmem : (∀ i ∈ Finset.univ, ![p₁, p₂, p₃] i ∈ s) := by
    intro i
    fin_cases i
    all_goals simpa
  convert (ConvexOn.map_sum_le hf h₀ h₁ hmem)
  all_goals simp [Fin.sum_univ_three]

/- Jensen's inequality for the average of three points. -/
theorem ConvexOn.map_sum_le_fin_three_real' {p₁ p₂ p₃ : ℝ} (hf : ConvexOn ℝ s f)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) :
    f (((1 : ℝ) / 3) • p₁ + ((1 : ℝ) / 3) • p₂ + ((1 : ℝ) / 3) • p₃) ≤
    ((1 : ℝ) / 3) • f p₁ + ((1 : ℝ) / 3) • f p₂ + ((1 : ℝ) / 3) • f p₃ := by
  refine @ConvexOn.map_sum_le_fin_three_real _ _ ((1 : ℝ) / 3) ((1 : ℝ) / 3) ((1 : ℝ) / 3) _ _ _ hf ?_ ?_ ?_ hp₁ hp₂ hp₃ ?_
  all_goals norm_num

end inequalities_95940

open inequalities_95940

/- Prove that if $a$, $b$, and $c$ are positive real numbers, then
$a^ab^bc^c\ge (abc)^{(a+b+c)/3}$ -/
theorem inequalities_95940 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ a * b ^ b * c ^ c ≥ (a * b * c) ^ ((a + b + c) / 3) := by
  -- Consider the function $f(x)=x\ln{x}$. $f''(x)=\frac{1}{x}&gt;0$ for $x&gt;0$ therefore, it is a convex function.
  have h0 := convexOn_mul_log
  -- We can apply Jensen's Inequality:
  -- $\frac{a\ln{a}+b\ln{b}+c\ln{c}}{3} \ge \left(\frac{a+b+c}{3}\right)\ln\left(\frac{a+b+c}{3}\right)$
  have h1 : 1 / 3 * (a + b + c) * log (1 / 3 * (a + b + c)) ≤ 1 / 3 * (a * log a + b * log b + c * log c) := by
    calc
    _ = (((1 : ℝ) / 3) • a + ((1 : ℝ) / 3) • b + ((1 : ℝ) / 3) • c) * log (((1 : ℝ) / 3) • a + ((1 : ℝ) / 3) • b + ((1 : ℝ) / 3) • c) := by
      simp only [smul_eq_mul]
      ring_nf
    _ ≤ ((1 : ℝ) / 3) • (a * log a) + ((1 : ℝ) / 3) • (b * log b) + ((1 : ℝ) / 3) • (c * log c) := by
      refine @ConvexOn.map_sum_le_fin_three_real' _ _ a b c h0 ?_ ?_ ?_
      all_goals simp only [Set.mem_Ici]
      · exact ha.le
      · exact hb.le
      · exact hc.le
    _ = _ := by
      simp only [smul_eq_mul]
      ring_nf
  -- Then $ \left(\frac{a+b+c}{3}\right)\ln\left(\sqrt[3]{abc}\right) \le \frac{a\ln{a}+b\ln{b}+c\ln{c}}{3}$
  have h2 : 1 / 3 * (a + b + c) * log (a ^ ((1 : ℝ) / 3) * b ^ ((1 : ℝ) / 3) * c ^ (((1 : ℝ) / 3))) ≤
      1 / 3 * (a + b + c) * log (1 / 3 * (a + b + c)) := by
    gcongr 1 / 3 * (a + b + c) * ?_
    gcongr log (?_)
    calc
      _ ≤ 1 / 3 * a + 1 / 3 * b + 1 / 3 * c := by
        refine Real.geom_mean_le_arith_mean3_weighted ?_ ?_ ?_ ha.le hb.le hc.le ?_
        -- by applying AM-GM inequality
        <;> norm_num
      _ = _ := by ring
  -- Rearranging,
  -- $\left(\frac{a+b+c}{3}\right)\ln\left(abc\right) \le a\ln{a}+b\ln{b}+c\ln{c}$
  have h3 : 1 / 3 * (a + b + c) * log (a * b * c) ≤ a * log a + b * log b + c * log c := by
    calc
      _ = 1 / 3 * (a + b + c) * (3 * log (a ^ ((1 : ℝ) / 3) * b ^ ((1 : ℝ) / 3) * c ^ (((1 : ℝ) / 3)))) := by
        congr 1
        have : a ^ ((1 : ℝ) / 3) * b ^ ((1 : ℝ) / 3) * c ^ (((1 : ℝ) / 3)) = (a * b * c) ^ ((1 : ℝ) / 3) := by
          rw [mul_rpow (by positivity) hc.le, mul_rpow ha.le hb.le]
        rw [this, log_rpow (by positivity)]
        ring
      _ = 3 * (1 / 3 * (a + b + c) * log (a ^ ((1 : ℝ) / 3) * b ^ ((1 : ℝ) / 3) * c ^ (((1 : ℝ) / 3)))) := by ring
      _ ≤ 3 * (1 / 3 * (a + b + c) * log (1 / 3 * (a + b + c))) := by
        apply mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 3 * (1 / 3 * (a * log a + b * log b + c * log c)) := by
        apply mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = _ := by simp
  -- Because $f(x) = e^x$ is an increasing function, we can conclude that:
  -- ${e}^{\ln\left(abc\right)(a+b+c)/3} \le e^{a\ln{a}+b\ln{b}+c\ln{c}}$
  have h4 : exp (1 / 3 * (a + b + c) * log (a * b * c)) ≤ exp (a * log a + b * log b + c * log c) :=
    exp_le_exp.mpr h3
  rw [ge_iff_le]
  -- which simplifies to the desired inequality
  convert h4 using 1
  · rw [← Real.log_rpow (by positivity), exp_log (by positivity)]
    congr 1
    ring
  · rw [exp_add, exp_add]
    repeat rw [← Real.log_rpow (by positivity)]
    repeat rw [exp_log (by positivity)]
