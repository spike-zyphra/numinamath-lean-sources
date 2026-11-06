import Mathlib

open Real Set

theorem algebra_167924 : {a : ℝ | {y : ℝ | ∃ x, y = Real.logb 10 (a * x^2 + 2 * x + 1) ∧ a * x^2 + 2 * x + 1 > 0} = Set.univ} = Set.Icc 0 1 := by
  ext a; simp
  constructor
  · intro h₁
    rw [Set.ext_iff] at h₁
    simp at h₁
    split_ands
    · by_contra! h₂
      -- when a < 0, then a * x^2 + 2 * x + 1 ≤ 1 - 1/a
      specialize h₁ (logb 10 (2 - 1 / a))
      obtain ⟨x, hx₁, hx₂⟩ := h₁
      have hx₃ : a * x^2 + 2 * x + 1 / a - 1 = 0 := by
        have : (10 : ℝ)^(logb 10 (2 - 1 / a)) = 10^(logb 10 (a * x ^ 2 + 2 * x + 1)) := by rw [hx₁]
        rw [rpow_logb, rpow_logb] at this
        repeat linarith
        field_simp
        exact lt_trans (one_div_neg.mpr h₂) (by positivity)
      have hx₄ : a * x^2 + 2 * x + 1 / a - 1 ≠ 0 := by
        suffices a * (x * x) + 2 * x + (1 / a - 1) ≠ 0 by
          rw [show a * x ^ 2 + 2 * x + 1 / a - 1 = a * (x * x) + 2 * x + (1 / a - 1) by ring_nf]
          exact this
        apply quadratic_ne_zero_of_discrim_ne_sq
        rw [discrim]
        intro s hs
        have h₄ : s^2 < 0 := by
          rw [hs.symm, mul_sub, mul_div, mul_one, ←mul_div, div_self (by linarith)]
          linarith
        linarith [sq_nonneg s]
      contradiction
    · by_contra! h₂
      -- when a > 1, then a * x^2 + 2 * x + 1 ≥ 1 - 1/a
      specialize h₁ (logb 10 ((a - 1) / (2 * a)))
      obtain ⟨x, hx₁, hx₂⟩ := h₁
      have hx₃ : a * x^2 + 2 * x + (a + 1) / (2 * a) = 0 := by
        have : (10 : ℝ)^(logb 10 ((a - 1) / (2 * a))) = 10^(logb 10 (a * x ^ 2 + 2 * x + 1)) := by rw [hx₁]
        rw [rpow_logb, rpow_logb] at this
        field_simp at this ⊢
        ring_nf at this ⊢
        repeat linarith
        field_simp
        linarith
      have hx₄ : a * x^2 + 2 * x + (a + 1) / (2 * a) ≠ 0 := by
        rw [pow_two]
        apply quadratic_ne_zero_of_discrim_ne_sq
        rw [discrim]
        intro s hs
        have h₄ : s^2 < 0 := by
          rw [←hs, show 4 * a * ((a + 1) / (2 * a)) = 2 * (a + 1) by field_simp [mul_div]; ring]
          linarith
        linarith [sq_nonneg s]
      contradiction
  · rintro ⟨h₁, h₂⟩
    ext y; simp
    obtain ⟨x, hx⟩ := show ∃ x, 10^y = a * x^2 + 2 * x + 1 by
      by_cases h₃ : a = 0
      · use (10^y - 1) / 2
        rw [h₃]
        field_simp
      have h₄ : discrim a 2 (1 - 10^y) ≥ 0 := by
        rw [discrim]
        field_simp
        suffices a * (1 - 10^y) ≤ 1 * 1 by linarith
        refine mul_le_mul_of_nonneg h₂ ?_ h₁ (by positivity)
        field_simp
        positivity
      have h₅ : ∃ s, discrim a 2 (1 - 10^y) = s * s := by
        use √(discrim a 2 (1 - 10^y))
        rw [←pow_two, Real.sq_sqrt]
        linarith
      obtain ⟨x, hx⟩ := exists_quadratic_eq_zero h₃ h₅
      use x
      linarith
    use x
    rw [hx.symm]
    field_simp
    apply Real.rpow_pos_of_pos (by positivity)
