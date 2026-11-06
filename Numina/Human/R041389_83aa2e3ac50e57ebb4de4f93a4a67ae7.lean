import Mathlib

/- 1. Let $n$ be a natural number, $a, b$ be positive real numbers, and satisfy $a+b=2$, then the minimum value of $\frac{1}{1+a^{n}}+\frac{1}{1+b^{n}}$ is $\qquad$. -/
theorem inequalities_150644 (n : ℕ) :
    IsLeast {x | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 2 ∧ x = 1 / (1 + a ^ n) + 1 / (1 + b ^ n)} 1
  := by
    constructor
    -- a = b = 1, achieves a value of 1
    · simp only [one_div, exists_and_left, Set.mem_setOf_eq]
      refine ⟨1, by linarith only, ?_⟩
      refine ⟨1, by linarith only, ?_, ?_⟩
      linarith only
      ring
    -- then we show that 1 is a lower bound
    · simp only [mem_lowerBounds, one_div, exists_and_left,
        Set.mem_setOf_eq, forall_exists_index, and_imp]
      intro x a a_pos b b_pos sum eq
      subst eq

      -- 1 / 2 is positive
      have half_pos : (0 : ℝ) ≤ (1 / 2) := by positivity

      -- a and b are non-negative
      have a_nonneg : 0 ≤ a := by positivity
      have b_nonneg : 0 ≤ b := by positivity

      -- we have a * b ≤ ((a + b) / 2) ^ 2, using AM-GM
      have am_gm : (a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) ≤ (1 / 2 * a + 1 / 2 * b) ^ (2 : ℝ) := by
        apply Real.rpow_le_rpow
        positivity
        exact Real.geom_mean_le_arith_mean2_weighted
          half_pos half_pos a_nonneg b_nonneg (by ring)
        linarith only
      have a_sq_pos : 0 ≤ a ^ ((1 : ℝ) / 2) := by positivity
      have b_sq_pos : 0 ≤ b ^ ((1 : ℝ) / 2) := by positivity
      rw [Real.mul_rpow a_sq_pos b_sq_pos] at am_gm
      simp only [one_div] at am_gm
      have a_pos : 0 ≤ a := by positivity
      have b_pos : 0 ≤ b := by positivity
      have two_ne_zero : (2 : ℝ) ≠ 0 := by positivity
      rw [Real.rpow_inv_rpow a_pos two_ne_zero,
        Real.rpow_inv_rpow b_pos two_ne_zero, ←mul_add] at am_gm

      -- but a + b = 2, so a * b ≤ 1
      simp only [sum, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        IsUnit.inv_mul_cancel, Real.rpow_two, one_pow] at am_gm

      -- then we can chain inequalities
      calc 1
      _ ≤ (1 + a ^ n + b ^ n + 1) / (1 + a ^ n + b ^ n + a ^ n * b ^ n) := by
        -- division is larger than one if numerator is larger than denominator
        rw [one_le_div₀ (by positivity)]
        -- most parts are equal, just look at non-equal term
        gcongr
        rw [←mul_pow]
        -- we use a * b ≤ 1 to show that (a * b) ^ n ≤ 1
        exact pow_le_one₀ (by positivity) am_gm
      -- simplify
      _ = (1 + a ^ n)⁻¹ + (1 + b ^ n)⁻¹ := by
        rw [←one_div, ←one_div, (div_add_div _ _ (by positivity) (by positivity))]
        ring