import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_204018 (f : ℝ → ℝ)
  (h₀ : ∀ x > 0, f x = x^2 + 3 * x + 6 / x + 4 / x^2 - 1) :
  IsLeast {y | ∃ x > 0, f x = y} (3 + 6 * sqrt 2) := by
  constructor
  · -- We verify that 3 + 6 * sqrt 2 is achieved by f at sqrt 2
    use Real.sqrt 2
    constructor
    · -- Show that sqrt(2) > 0
      positivity
    · -- Show that f sqrt 2 = 3 + 6 * sqrt 2
      rw [h₀ (Real.sqrt 2) (by positivity)]
      have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp [h1]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · -- We need to show that 3 + 6 * sqrt 2 is the minimum
    rintro y ⟨x, hx, h_eq⟩
    rw [h₀ x hx] at h_eq
    have h1 : x ^ 2 + 4 / x ^ 2 ≥ 4 := by
      have h2 : x ^ 2 + 4 / x ^ 2 - 4 ≥ 0 := by
        have h3 : x ^ 2 + 4 / x ^ 2 - 4 = (x ^ 4 + 4 - 4 * x ^ 2) / x ^ 2 := by
          field_simp
          ring
        rw [h3]
        have h4 : x ^ 2 > 0 := by
          nlinarith [sq_pos_of_pos hx]
        have h5 : x ^ 4 + 4 - 4 * x ^ 2 ≥ 0 := by
          nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2), sq_nonneg (x - 2 / x), sq_nonneg (x * (x - 2 / x)), sq_nonneg (x * (x - 2)), sq_nonneg ((2 / (x : ℝ)) * (x - 2)), Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]
        apply div_nonneg
        linarith
        positivity
      linarith
    have h2 : 3 * x + 6 / x ≥ 6 * Real.sqrt 2 := by
      have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h5 : 3 * x + 6 / x - 6 * Real.sqrt 2 ≥ 0 := by
        have h6 : 3 * x + 6 / x - 6 * Real.sqrt 2 = (3 * x ^ 2 + 6 - 6 * Real.sqrt 2 * x) / x := by
          field_simp
          ring
        rw [h6]
        have hx2 : x > 0 := by linarith
        have h7 : 3 * x ^ 2 + 6 - 6 * Real.sqrt 2 * x ≥ 0 := by
          nlinarith [sq_nonneg (x - Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, sq_nonneg (x * Real.sqrt 2 * (x * Real.sqrt 2)), Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2
          ]
        apply div_nonneg
        linarith
        positivity
      linarith
    have h3 : x ^ 2 + 3 * x + 6 / x + 4 / x^2 - 1 ≥ 3 + 6 * Real.sqrt 2 := by
      linarith
    linarith [h_eq, h3]