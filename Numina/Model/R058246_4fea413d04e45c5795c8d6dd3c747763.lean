import Mathlib

theorem algebra_214612 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.logb 2 (x + y) ^ 2 + Real.logb 2 (x * y) ^ 2 + 1 = 2 * Real.logb 2 (x + y) ↔ x = 1 ∧ y = 1 := by
  constructor
  · -- Forward implication: equation implies (1,1)
    intro h_eq
    have h1 : Real.logb 2 (x + y) ^ 2 - 2 * Real.logb 2 (x + y) + 1 + Real.logb 2 (x * y) ^ 2 = 0 := by
      nlinarith
    have h2 : (Real.logb 2 (x + y) - 1) ^ 2 + Real.logb 2 (x * y) ^ 2 = 0 := by
      nlinarith
    have h3 : (Real.logb 2 (x + y) - 1) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h4 : Real.logb 2 (x * y) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h5 : (Real.logb 2 (x + y) - 1) ^ 2 = 0 := by
      linarith
    have h6 : Real.logb 2 (x * y) ^ 2 = 0 := by
      linarith
    have h7 : Real.logb 2 (x * y) = 0 := by
      rw [sq_eq_zero_iff] at h6
      exact h6
    have h8 : Real.logb 2 (x + y) - 1 = 0 := by
      rw [sq_eq_zero_iff] at h5
      exact h5
    have h9 : Real.logb 2 (x + y) = 1 := by linarith
    have h10 : x * y = 1 := by
      rw [Real.logb_eq_iff_rpow_eq] at h7
      · nlinarith
      all_goals nlinarith
    have h11 : x + y = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] at h9
      · nlinarith
      all_goals nlinarith
    have h12 : x = 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), h10, h11]
    have h13 : y = 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), h10, h11]
    exact ⟨h12, h13⟩
  · -- Backward implication: (1,1) satisfies equation
    rintro ⟨rfl, rfl⟩
    norm_num [Real.logb_mul, Real.logb_self_eq_one]
    all_goals linarith