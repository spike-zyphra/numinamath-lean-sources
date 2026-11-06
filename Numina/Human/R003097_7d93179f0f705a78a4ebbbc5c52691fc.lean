import Mathlib

open Real

/- ## Problem Statement

Based on the definition of the derivative, find $f^{\prime}(0)$:
$$
f(x)=\left\{\begin{array}{c}
e^{x \sin 5 x}-1, x \neq 0 \\
0, x=0
\end{array}\right.
$$
 -/
theorem calculus_152885 (f : ℝ → ℝ)
    (h₀ : ∀ x, x ≠ 0 → f x = Real.exp (x * Real.sin (5 * x)) - 1)
    (h₁ : f 0 = 0) :
    HasDerivAt f 0 0 := by
  -- Use the definition of the derivative and rewrite the goal as
  -- Tendsto (fun x => x⁻¹ * (f x - f 0)) (𝓝[≠] 0) 0.
  simp [hasDerivAt_iff_tendsto_slope, slope_fun_def, h₁]
  -- Show that for any e > 0 there exists a neighborhood s in 𝓝[≠] 0 such that
  -- |x⁻¹ * f x| < e for all x ∈ s.
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro e he
  -- Define e' = min (e / 10) 1
  set e' := min (e / 10) 1
  have he' : e' > 0 := by simp [e', he]
  have ⟨he1, he2⟩ : e' ≤ 1 ∧ e' ≤ e / 10 := by simp [e']
  rw [Filter.eventually_iff_exists_mem]
  -- Take the following neighborhood: (-e', e') \ {0}.
  use Set.Ioo (-e') e' \ {0}
  constructor
  · rw [Set.diff_eq, Set.inter_comm]
    apply inter_mem_nhdsWithin
    apply Ioo_mem_nhds (by linarith) he'
  simp
  intro x hx1 hx2 hx0
  rw [h₀ x hx0]
  -- Show that |x|⁻¹ * |exp(x * sin(5 * x)) - 1| < e for x ∈ (-e', e'), x ≠ 0.
  calc
    -- We have |exp y - 1| ≤ 2 * |y| for all |y| ≤ 1 so we get
    -- |exp(x * sin(5 * x)) - 1| ≤ 2 * |x * sin(5 * x)|.
    |x|⁻¹ * |exp (x * sin (5 * x)) - 1| ≤ |x|⁻¹ * (2 * |x * sin (5 * x)|) := by
        gcongr
        apply abs_exp_sub_one_le
        rw [abs_mul, ← mul_one (1 : ℝ)]
        gcongr
        · rw [abs_le]
          constructor <;> linarith
        · exact abs_sin_le_one (5 * x)
    -- |x|⁻¹ * 2 * |x * sin(5 * x)| = 2 * |sin(5 * x)|.
    _ = 2 * |sin (5 * x)| := by
        field_simp [abs_mul]
        ring
    -- |sin(5 * x)| ≤ |5 * x| for all x.
    _ ≤ 2 * |5 * x| := by
        apply mul_le_mul (le_refl 2) _ (abs_nonneg _) zero_le_two
        apply abs_sin_le_abs
    -- |x| < e / 10.
    _ < 2 * 5 * (e / 10) := by
        simp only [abs_mul, Nat.abs_ofNat, ← mul_assoc]
        gcongr
        rw [abs_lt]
        constructor <;> linarith
    -- 2 * 5 * (e / 10) = e.
    _ = e := by ring