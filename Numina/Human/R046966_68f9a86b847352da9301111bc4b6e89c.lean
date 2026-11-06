import Mathlib

open Real Set

/- ## Condition of the problem

Calculate the definite integral:


$$

\int_{\pi / 4}^{\operatorname{arctg} 3} \frac{1+\operatorname{ctg} x}{(\sin x+2 \cos x)^{2}} d x

$$
 -/
theorem calculus_157153 :
    ∫ x in (π/4)..(arctan 3), (1 + cot x) / (sin x + 2 * cos x)^2 =
    log (9/5)/4 + 1/15 := by
  -- cot(x) = 1 / tan(x).
  have hcot x : cot x = 1 / tan x := by
    rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos, one_div, inv_div]
  have huIcc : Set.uIcc (1 : ℝ) 3 = Set.Icc 1 3 := by simp only [Nat.one_le_ofNat, uIcc_of_le]
  -- Show that arctan '' [1, 3] = [arctan 1, arctan 3] = [π / 4, arctan 3].
  have hatanIcc : arctan '' Set.Icc 1 3 = Set.Icc (π / 4) (arctan 3) := by
    rw [Set.Subset.antisymm_iff, ← arctan_one]
    constructor
    -- We have arctan '' [1, 3] ⊆ [arctan 1, arctan 3] because arctan is monotone.
    · apply Monotone.image_Icc_subset
      apply arctan_strictMono.monotone
    -- We have [arctan 1, arctan 3] ⊆ arctan '' [1, 3] because arctan is continuous.
    · apply intermediate_value_Icc (by norm_num)
      apply continuous_arctan.continuousOn
  -- arctan 3 < π / 2.
  have hatan3 : arctan 3 < π / 2 := arctan_lt_pi_div_two 3
  simp_rw [← arctan_one, hcot]
  -- Change the integral variable. Let x = arctan t.
  -- We get the following integral to compute:
  -- ∫ (x : ℝ) in 1 ..3, (1 / (1 + x ^ 2)) • ((fun x ↦ (1 + 1 / tan x) / (sin x + 2 * cos x) ^ 2) ∘ arctan) x
  rw [← intervalIntegral.integral_comp_smul_deriv' (fun x _ => hasDerivAt_arctan x)]
  rotate_left
  -- We need to show that the derivative of arctan is continuous.
  · exact ContinuousOn.div (by fun_prop) (by fun_prop) (fun _ _ => by positivity)
  -- We need to show that (1 + 1 / tan x) / (sin x + 2 * cos x) ^ 2
  -- is continuous on [π / 4, arctan 3].
  · rw [huIcc, hatanIcc]
    apply ContinuousOn.div _ (by fun_prop)
    -- Show that sin x + 2 * cos x ≠ 0 for x ∈ [π / 4, arctan 3].
    · simp only [mem_Icc, pow_eq_zero_iff, and_imp]
      intro x hx1 hx2
      apply ne_of_gt
      apply pow_pos
      apply add_pos
      · apply sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      · apply mul_pos (by norm_num)
        apply cos_pos_of_mem_Ioo
        simp only [mem_Ioo]
        constructor <;> linarith
    -- Show that tan(x) ≠ 0 for x ∈ [π / 4, arctan 3] and tan(x) is continuous on this interval.
    · apply ContinuousOn.add (by fun_prop)
      simp only [one_div, huIcc]
      apply ContinuousOn.inv₀
      · apply continuousOn_tan_Ioo.mono
        apply Set.Icc_subset_Ioo (by linarith [pi_pos]) (by linarith)
      · simp only [mem_Icc, and_imp]
        intro x hx1 hx2
        apply ne_of_gt
        apply tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  -- We have (sin x + 2 * cos x) ^ 2 = 1 + 3 * cos x ^ 2 + 2 * sin (2 * x).
  -- This result follows from sin x ^ 2 + cos x ^ 2 = 1 and sin (2 * x) = 2 * sin x * cos x.
  have heq1 x : (sin x + 2 * cos x) ^ 2 = 1 + 3 * cos x ^ 2 + 2 * sin (2 * x) := by
    rw [sin_two_mul]
    linear_combination (sin_sq_add_cos_sq x)
  -- We have sin (2 * x) = 2 * tan x / (1 + tan x ^ 2) for all x.
  have heq2 x : sin (2 * x) = 2 * tan x / (1 + tan x ^ 2) := by
    rw [tan_eq_sin_div_cos]
    by_cases h : cos x = 0
    · simp [h]
      -- If cos x = 0 then we need to show that sin (2 * x) = 0.
      rw [cos_eq_zero_iff] at h
      have ⟨k, hk⟩ := h
      rw [hk, show 2 * ((2 * k + 1) * π / 2) = (2 * k + 1 : ℤ) * π by simp; ring]
      rw [sin_int_mul_pi]
    -- If cos x ≠ 0 then everything follows from sin x ^ 2 + cos x ^ 2 = 1 and
    -- sin (2 * x) = 2 * sin x * cos x.
    field_simp [sin_two_mul]
    ring
  -- Use identities heq1, heq2 and the following properties of trigonometric functions:
  -- tan (arctan x) = x, cos (arctan x) = 1 / √(1 + x ^ 2).
  simp only [heq1, heq2]
  simp only [Function.comp_apply, tan_arctan, smul_eq_mul, cos_arctan, div_pow]
  -- Let g(x) = 1 / 4 * (1 / x - 1 / (x + 2) + 2 * (1 / (x + 2)^2)).
  -- Show that the function under integral is equal to g(x) for x ∈ [1, 3].
  set g : ℝ → ℝ := fun x => 1 / 4 * (1 / x - 1 / (x + 2) + 2 * (1 / (x + 2)^2))
  rw [intervalIntegral.integral_congr (g := g)]
  rotate_left
  · intro x
    simp only [Nat.one_le_ofNat, uIcc_of_le, mem_Icc, one_pow, and_imp, g]
    intro hx1 hx2
    rw [sq_sqrt (by positivity)]
    field_simp
    ring
  -- It is left to compute the integral
  -- ∫ x in 1..3, g(x) = 1 / 4 * (∫ x in 1..3, 1 / x - ∫ x in 3..5, 1 / x + 2 * ∫ x in 3..5, x^(-2)).
  simp only [intervalIntegral.integral_const_mul, g]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub]
  rotate_left
  -- Show that 1 / x, 1 / (x + 2), and 1 / (x + 2)^2 are integrable.
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    simp only [huIcc, mem_Icc, ne_eq, and_imp]
    intro x hx1 hx3
    linarith
  · apply ContinuousOn.intervalIntegrable
    simp
    apply ContinuousOn.inv₀ (by fun_prop)
    simp
    intro x hx1 hx2
    linarith
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.sub
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      simp only [huIcc, mem_Icc, ne_eq, and_imp]
      intro x hx1 hx3
      linarith
    · simp
      apply ContinuousOn.inv₀ (by fun_prop)
      simp
      intro x hx1 hx2
      linarith
  · apply ContinuousOn.intervalIntegrable
    simp
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.inv₀ (by fun_prop)
    simp
    intro x hx1 hx2
    linarith
  -- ∫ x in a..b, 1 / x = log (b / a) for a > 0 and b > 0.
  rw [integral_one_div_of_pos (by norm_num) (by norm_num)]
  rw [intervalIntegral.integral_comp_add_right, integral_one_div_of_pos (by norm_num) (by norm_num)]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_add_right (fun x => 1 / x ^ 2)]
  have heq3 (x : ℝ) : 1 / x ^ 2 = x ^ (-2 : ℤ) := by
    simp only [one_div, Int.reduceNeg, zpow_neg, inv_inj]
    rw [zpow_two, pow_two]
  simp only [heq3]
  -- ∫ x in 3..5, x^(-2) = (5⁻¹ - 3⁻¹) / (-1).
  rw [integral_zpow]
  swap
  · right
    simp
    norm_num
  norm_num
  -- After simplifications, we get 1 / 4 * (log 3 - log (5 / 3) + 4 / 15) = log (9 / 5) / 4 + 1 / 15.
  repeat rw [log_div (by norm_num) (by norm_num)]
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]
  ring