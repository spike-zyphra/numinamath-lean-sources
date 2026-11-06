import Mathlib 

theorem algebra_5180 (k : ℤ) :
  (∃ x₁ x₂ : ℤ, x₁ ≠ x₂ ∧ x₁^3 - 27 * x₁ + k = 0 ∧ x₂^3 - 27 * x₂ + k = 0) ↔ k = 54 ∨ k = -54 := by 
  constructor
  · -- Assume there are two distinct integer roots, prove k = ±54
    rintro ⟨x₁, x₂, h₁₂, h₁, h₂⟩
    have h3 : x₁^2 + x₁ * x₂ + x₂^2 = 27 := by
      have h4 : x₁^3 - 27 * x₁ + k = 0 := h₁
      have h5 : x₂^3 - 27 * x₂ + k = 0 := h₂
      have h6 : x₁^3 - 27 * x₁ + k - (x₂^3 - 27 * x₂ + k) = 0 := by
        rw [h4, h5]
        all_goals ring
      have h7 : (x₁ - x₂) * (x₁^2 + x₁ * x₂ + x₂^2 - 27) = 0 := by
        nlinarith
      cases (mul_eq_zero.1 h7) with
      | inl h8 =>
        -- This would mean x₁ - x₂ = 0, but x₁ ≠ x₂ so contradiction
        exfalso
        apply h₁₂
        linarith
      | inr h9 =>
        linarith
    have h8 : x₂ ≤ 6 := by
      nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂), sq_nonneg (x₁ + 3), sq_nonneg (x₂ + 3), sq_nonneg (x₁ - 3), sq_nonneg (x₂ - 3)]
    have h9 : x₂ ≥ -6 := by
      nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂), sq_nonneg (x₁ + 3), sq_nonneg (x₂ + 3), sq_nonneg (x₁ - 3), sq_nonneg (x₂ - 3)]
    have h10 : x₁ ≤ 6 := by
      nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂), sq_nonneg (x₁ + 3), sq_nonneg (x₂ + 3), sq_nonneg (x₁ - 3), sq_nonneg (x₂ - 3)]
    have h11 : x₁ ≥ -6 := by
      nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂), sq_nonneg (x₁ + 3), sq_nonneg (x₂ + 3), sq_nonneg (x₁ - 3), sq_nonneg (x₂ - 3)]
    interval_cases x₁ <;> interval_cases x₂ <;> omega
  · -- Assume k = 54 or k = -54, prove existence of two distinct integer roots
    rintro (hk | hk)
    · -- k = 54, use roots 3 and -6
      rw [hk]
      use 3, -6
      all_goals norm_num
    · -- k = -54, use roots 6 and -3
      rw [hk]
      use 6, -3
      all_goals norm_num