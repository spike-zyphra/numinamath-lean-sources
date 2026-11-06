import Mathlib

theorem algebra_15211 :
    {x | 0 < x ∧ (1 / 2) * (3 * x ^ 2 - 1) = (x ^ 2 - 50 * x - 10) * (x ^ 2 + 25 * x + 5)} = {25 + 2 * Real.sqrt 159} :=  by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Forward implication: assume x is a positive solution; prove x = 25 + 2√159
    intro h
    rcases h with ⟨hx_pos, heq⟩
    have h1 : 2 * x ^ 4 - 50 * x ^ 3 - 2513 * x ^ 2 - 1000 * x - 99 = 0 := by
      nlinarith
    have h2 : (2 * x ^ 2 + 50 * x + 9) * (x ^ 2 - 50 * x - 11) = 0 := by
      nlinarith [h1]
    cases (mul_eq_zero.1 h2) with
    | inl h3 =>
      have h4 : 2 * x ^ 2 + 50 * x + 9 = 0 := by
        linarith
      -- To prove that quadratics have no positive roots
      nlinarith [sq_nonneg (x + 50 / 2), Real.sqrt_nonneg 159]
    | inr h4 =>
      have h4' : (x ^ 2 - 50 * x - 11) = 0 := by
        linarith
      have h5 : (x - (25 + 2 * Real.sqrt 159)) * (x - (25 - 2 * Real.sqrt 159)) = 0 := by
        nlinarith [h4', Real.sqrt_nonneg 159, Real.sqrt_nonneg 159, sq_nonneg (x ^ 2 - 50 * x - 11), Real.sq_sqrt (show (0 : ℝ) ≤ 159 by norm_num)]
      cases (mul_eq_zero.1 h5) with
      | inl h6 =>
        linarith
      | inr h7 =>
        -- Case where x = 25 - 2 * sqrt(159), which contradicts x > 0
        nlinarith [Real.sqrt_nonneg 159, Real.sq_sqrt (show (0 : ℝ) ≤ (159 : ℝ) by norm_num), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (159 : ℝ)), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (159 : ℝ))]
  · -- Reverse direction: show that 25 + 2√159 is a positive solution
    intro h
    rw [h]
    constructor
    · -- Show positivity
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (159 : ℝ)), Real.sqrt_nonneg 159, Real.sq_sqrt (show (0 : ℝ) ≤ 159 by norm_num)]
    · -- Show equality
      nlinarith [Real.sqrt_nonneg 159, Real.sqrt_nonneg 159, Real.sq_sqrt (show (0 : ℝ) ≤ 159 by norm_num), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (159 : ℝ)), Real.sqrt_nonneg 159]