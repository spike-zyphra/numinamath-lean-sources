import Mathlib

open Real

/- ## Condition of the problem
Calculate the definite integral:
$$
\int_{\pi / 4}^{\arcsin (2 / \sqrt{5})} \frac{4 \operatorname{tg} x-5}{4 \cos ^{2} x-\sin 2 x+1} d x
$$
 -/
theorem calculus_157431 :
    ∫ x in (π/4)..(arcsin (2/sqrt 5)), (4*tan x - 5)/(4*(cos x)^2 - sin (2*x) + 1) =
    2*log (5/4) - (1/2)*arctan (1/2) := by
  rw [← arctan_one]
  -- We have arcsin (2 / √5) = arctan 2.
  have eq : arcsin (2 / √5) = arctan 2 := by
    rw [arctan_eq_arcsin]
    norm_num
  have huIcc : Set.uIcc (1 : ℝ) 2 = Set.Icc 1 2 := by
    simp only [Nat.one_le_ofNat, Set.uIcc_of_le]
  have hatanIcc : arctan '' Set.Icc 1 2 = Set.Icc (π / 4) (arctan 2) := by
    rw [Set.Subset.antisymm_iff, ← arctan_one]
    constructor
    -- We have arctan '' [1, 2] ⊆ [arctan 1, arctan 2] because arctan is monotone.
    · apply Monotone.image_Icc_subset
      apply arctan_strictMono.monotone
    -- We have [arctan 1, arctan 2] ⊆ arctan '' [1, 2] because arctan is continuous.
    · apply intermediate_value_Icc (by norm_num)
      apply continuous_arctan.continuousOn
  -- Change the integral variable. Let x = arctan t.
  -- We get the following integral to compute:
  -- ∫ (x : ℝ) in 1 ..2, (1 / (1 + x ^ 2)) • ((fun x ↦ (4 * tan x - 5) / (4 * cos x ^ 2 - sin (2 * x) + 1)) ∘ arctan) x.
  rw [eq, ← intervalIntegral.integral_comp_smul_deriv' (fun x _ => hasDerivAt_arctan x)]
  rotate_left
  -- Show that 1 / (1 + x^2) is continuous on [1, 2].
  · apply Continuous.continuousOn
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    positivity
  -- Show that (4 * tan x - 5)/(4 * (cos x)^2 - sin (2*x) + 1) is continuous
  -- on [arctan 1, arctan 2].
  · rw [huIcc, hatanIcc]
    apply ContinuousOn.div _ (by fun_prop)
    · simp only [Set.mem_Icc, ne_eq, and_imp]
      -- We need to show that 4 * (cos x)^2 - sin (2 * x) + 1 ≠ 0 for x ∈ [arctan 1, arctan 2].
      intro x hx1 hx2
      apply ne_of_gt
      rw [← add_zero 0, show 4 * cos x^2 - sin (2 * x) + 1 = 4 * cos x^2 + (1 - sin (2 * x)) by ring]
      apply add_lt_add_of_lt_of_le
      -- We have 4 * cos x ^ 2 > 0 for x ∈ [arctan 1, arctan 2] since
      -- 0 < arctan 1 < arctan 2 < π / 2.
      · apply mul_pos (by norm_num)
        apply pow_pos
        apply cos_pos_of_mem_Ioo
        simp only [Set.mem_Ioo]
        constructor <;> linarith [pi_pos, arctan_lt_pi_div_two 2]
      -- We have 1 - sin (2 * x) ≥ 0 for all x.
      · linarith [sin_le_one (2 * x)]
    -- Show that 4 * tan x - 5 is continuous on [arctan 1, arctan 2].
    · apply ContinuousOn.sub _ (by fun_prop)
      apply ContinuousOn.mul (by fun_prop)
      intro x
      simp only [Set.mem_Icc, and_imp]
      intro hx1 hx2
      apply ContinuousAt.continuousWithinAt
      rw [continuousAt_tan]
      -- It is enough to show that cos x ≠ 0 for x ∈ [arctan 1, arctan 2].
      apply ne_of_gt
      apply cos_pos_of_mem_Ioo
      simp only [Set.mem_Ioo]
      constructor <;> linarith [pi_pos, arctan_lt_pi_div_two 2]
  -- We have sin (2 * x) = 2 * tan x / (1 + tan x ^ 2) for all x.
  have hsin2 x : sin (2 * x) = 2 * tan x / (1 + tan x ^ 2) := by
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
  -- After simplifications we get the following integral to compute:
  -- ∫ (x : ℝ) in 1 ..2, 1 / (1 + x ^ 2) * ((4 * x - 5) / (4 * (1 / (1 + x ^ 2)) - 2 * x / (1 + x ^ 2) + 1)).
  simp only [hsin2, Function.comp_apply, tan_arctan, cos_sq_arctan, smul_eq_mul]
  have h1 (x : ℝ) (hx : x ∈ Set.Icc 1 2) : 1 + x ^ 2 ≠ 0 := by positivity
  -- Define f(x) = 2 * log (x ^ 2 - 2 * x + 5) - arctan ((x - 1) / 2) / 2.
  set f : ℝ → ℝ := fun x => 2 * log (x ^ 2 - 2 * x + 5) - arctan ((x - 1) / 2) / 2
  -- Prove that the derivative of f(x) is equal to the expression under the integral.
  have hdf x (hx : x ∈ Set.Ioo 1 2) : HasDerivAt f ((1 / (1 + x ^ 2) * ((4 * x - 5) / (4 * (1 / (1 + x ^ 2)) - 2 * x / (1 + x ^ 2) + 1)))) x := by
    simp only [Set.mem_Ioo] at hx
    replace eq : (1 / (1 + x ^ 2) * ((4 * x - 5) / (4 * (1 / (1 + x ^ 2)) - 2 * x / (1 + x ^ 2) + 1)))
        = 2 * ((2 * x ^ (2 - 1) * 1 - 2 * 1) / (x^2 - 2 * x + 5)) - (1 / (1 + ((x - 1) / 2)^2) * (1 / 2)) / 2 := by
      field_simp [show x^2 - 2 * x + 5 ≠ 0 by nlinarith, show 4 - 2 * x + (1 + x ^ 2) ≠ 0 by nlinarith]
      ring
    rw [eq]
    apply HasDerivAt.sub
    · apply HasDerivAt.const_mul
      apply HasDerivAt.log _ (by nlinarith)
      apply HasDerivAt.add_const
      apply HasDerivAt.sub _ (HasDerivAt.const_mul _ (hasDerivAt_id' x))
      apply HasDerivAt.pow _ (hasDerivAt_id' x)
    · apply HasDerivAt.div_const
      apply HasDerivAt.arctan
      apply HasDerivAt.div_const
      apply HasDerivAt.sub_const
      exact hasDerivAt_id' x
  -- Apply the fundamental theorem of calculus and get f(2) - f(1) as the value
  -- of the integral.
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) _ hdf]
  · simp [f]
    norm_num
    rw [log_div (by norm_num) (by norm_num)]
    ring
  -- It is left to show that f'(x) is integrable on [1, 2].
  -- It is enough to prove that f'(x) is continuous on [1, 2].
  · apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    apply ContinuousOn.mul (by fun_prop (disch := assumption))
    apply ContinuousOn.div (by fun_prop) (by fun_prop (disch := assumption))
    intro x hx
    field_simp
    nlinarith
  · apply ContinuousOn.sub
    · apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.log (by fun_prop)
      intro x hx
      nlinarith
    · apply Continuous.continuousOn
      apply Continuous.div_const
      apply Continuous.comp (g := arctan) continuous_arctan (by fun_prop)