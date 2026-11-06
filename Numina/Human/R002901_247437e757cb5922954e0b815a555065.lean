import Mathlib

open Real

/- ## Problem Statement
Calculate the definite integral:
$$
\int_{1}^{8} \frac{5 \sqrt{x+24}}{(x+24)^{2} \cdot \sqrt{x}} d x
$$
 -/
theorem calculus_127941 : ∫ x in (1)..8, 5 * sqrt (x + 24) / ((x + 24) ^ 2 * sqrt x) = 1 / 8 := by
  -- Define f(t) = 24 / (t^2 - 1).
  set f : ℝ → ℝ := fun t => 24 / (t^2 - 1)
  -- We have Set.uIcc 5 2 = Set.Icc 2 5.
  have hs : Set.uIcc (5 : ℝ) 2 = Set.Icc 2 5 := by rw [Set.uIcc_of_ge (by norm_num)]
  -- Show that 0 < f(x) for all x ∈ [2, 5].
  have hf_pos {x : ℝ} (hx : x ∈ Set.uIcc 5 2) : 0 < f x := by
    simp [hs, f, lt_abs] at hx ⊢
    left
    linarith
  -- Show that f'(x) = -x * f(x)^2 / 12 for all x ∈ [2, 5].
  have hdf x (hx : x ∈ Set.uIcc 5 2) : HasDerivAt f (-x * (f x)^2 / 12) x := by
    simp [hs] at hx
    have eq : -x * (f x)^2 / 12 = (0 * (x^2 - 1) - 24 * (2 * x^1)) / (x^2 - 1)^2 := by
      simp [f, div_pow]
      ring
    rw [eq]
    apply HasDerivAt.div (hasDerivAt_const _ _) _ (by nlinarith)
    apply HasDerivAt.sub_const (hasDerivAt_pow _ _)
  -- We have 1 = f(5) and 8 = f(2).
  nth_rw 1 [show 1 = f 5 by simp [f]; norm_num, show 8 = f 2 by simp [f]; norm_num]
  -- Change the integral variable with x = f(t).
  rw [← intervalIntegral.integral_comp_smul_deriv' hdf]
  rotate_left
  · -- Show that f'(x) is continuous on [2, 5].
    rw [hs]
    apply ContinuousOn.div_const
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.pow
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    -- It is enough to show that x^2 - 1 ≠ 0 for x ∈ [2, 5].
    simp
    intro x hx1 hx2
    nlinarith
  · -- Show that 5 * √(x + 24) / ((x + 24) ^ 2 * √x) is continuous
    -- on f '' [2, 5].
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    simp only [Set.mem_image, Set.mem_Icc, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, not_or, forall_exists_index, and_imp, f]
    intro x t ht heq
    replace hf_pos := hf_pos ht
    rw [show x = f t by simp [← heq]]
    -- It is enough to show that f(t) + 24 ≠ 0 and √f(t) ≠ 0 for t ∈ [2, 5].
    constructor <;> positivity
  simp only [neg_mul, Function.comp_apply, smul_eq_mul]
  -- Prove that the expression under the integral is equal to (-5 / 12) * x^(-2 : ℤ).
  have eq : Set.EqOn (fun x => -(x * f x^2) / 12 * (5 * √(f x + 24) / ((f x + 24) ^ 2 * √(f x))))
            (fun x => (-5 / 12) * x^(-2 : ℤ)) (Set.uIcc 5 2) := by
    intro x hx
    simp only [Int.reduceNeg, zpow_neg]
    replace hf_pos := hf_pos hx
    simp [hs] at hx
    have h0 : 0 < x^2 - 1 := by nlinarith
    -- Show that f(x) + 24 = x^2 * f(x).
    have eq : f x + 24 = x^2 * f x := by
      field_simp [f]
      ring
    -- Simplify the expression and get the result.
    rw [eq, sqrt_mul (by positivity), sqrt_sq (by linarith), ← mul_assoc]
    rw [mul_div_mul_right _ _ (by positivity), div_mul_div_comm]
    calc
      _ = (-5) * (x * f x)^2 / (12 * x^2 * (x * f x)^2) := by ring_nf
      _ = (-5) / (12 * x^2) := by
        rw [mul_div_mul_right]
        nlinarith
      _ = -5 / 12 * (x ^ 2)⁻¹ := by
        ring
  -- It is left to compute
  -- ∫ x in (5)..2, -5 / 12 * x^(-2) = -5 / 12 * ∫ x in (5)..2, x^(-2).
  rw [intervalIntegral.integral_congr eq]
  rw [intervalIntegral.integral_const_mul, integral_zpow (by simp [hs])]
  norm_num