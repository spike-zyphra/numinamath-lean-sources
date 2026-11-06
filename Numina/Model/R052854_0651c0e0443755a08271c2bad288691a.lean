import Mathlib

theorem algebra_252764 (x : ℝ) (hx : 5 - x ≥ 0) :
    Real.sqrt (5 - x) * (3^(x^2 - 7.2*x + 3.9) - 9 * Real.sqrt 3) = 0 ↔
    x = 5 ∨ x = 1 / 5 := by
  constructor
  · -- Assume sqrt(5 - x) * (3^(x^2 - 7.2*x + 3.9) - 9 * sqrt 3) = 0, prove x = 5 ∨ x = 1/5
    intro h
    cases' (mul_eq_zero.mp h) with h₁ h₂
    · -- Case where sqrt(5 - x) = 0
      have h3 : Real.sqrt (5 - x) = 0 := by linarith
      have h4 : 5 - x = 0 := by
        rw [Real.sqrt_eq_zero (by linarith)] at h3
        linarith
      left
      linarith
    · -- Case where 3^{x^2 - 7.2*x + 3.9} - 9 * sqrt 3 = 0
      have h3 : (3 : ℝ) ^ (x ^ 2 - 7.2 * x + 3.9) - 9 * Real.sqrt 3 = 0 := by linarith
      have h4 : (3 : ℝ) ^ (x ^ 2 - 7.2 * x + 3.9) = 9 * Real.sqrt 3 := by linarith
      have h5 : (9 * Real.sqrt 3) = (3 : ℝ) ^ (5 / 2 : ℝ) := by
        have h9 : (9 : ℝ) = 3 ^ (2 : ℝ) := by norm_num
        have hsqrt3 : Real.sqrt 3 = (3 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
        rw [h9, hsqrt3]
        rw [← Real.rpow_add]
        norm_num
        all_goals norm_num
        all_goals positivity
      rw [h5] at h4
      have h6 : x ^ 2 - 7.2 * x + 3.9 = (5 / 2 : ℝ) := by
        apply_fun (Real.logb (3 : ℝ)) at h4
        simp at h4 ⊢
        linarith
      have h10 : x ^ 2 - 7.2 * x + 1.4 = 0 := by
        nlinarith
      have h7 : (x - 1/5) * (x - 7) = 0 := by
        ring_nf at h10 ⊢
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- Case x = 1/5
        right
        linarith
      · -- Case x = 7
        have h10 : x = 7 := by linarith
        linarith [show 5 - x ≥ 0 from hx, h10]
  · -- Assume x = 5 ∨ x = 1/5, prove sqrt(5 - x) * (3^(x^2 - 7.2*x + 3.9) - 9 * sqrt 3) = 0
    rintro (h | h)
    · -- Case x = 5
      rw [h]
      norm_num
      <;> positivity
    · -- Case x = 1/5
      rw [h]
      have h1 : (3 : ℝ) ^ ((1 / 5 : ℝ)^2 - 7.2 * (1 / 5 : ℝ) + 3.9) = 9 * Real.sqrt 3 := by
        have h2 : (1 / 5 : ℝ)^2 - 7.2 * (1 / 5 : ℝ) + 3.9 = (5 / 2 : ℝ) := by
          norm_num
        rw [h2]
        have h3 : (3 : ℝ) ^ (5 / 2 : ℝ) = 9 * Real.sqrt 3 := by
          have h9 : (9 : ℝ) = 3 ^ (2 : ℝ) := by norm_num
          have hsqrt3 : Real.sqrt 3 = (3 : ℝ) ^ (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
          rw [h9, hsqrt3]
          rw [← Real.rpow_add]
          norm_num
          all_goals norm_num
          all_goals positivity
        linarith [h3]
      rw [h1]
      norm_num
      <;> positivity