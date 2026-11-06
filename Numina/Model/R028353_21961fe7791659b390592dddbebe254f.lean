import Mathlib

theorem algebra_308054 {A : ℝ} (hA : A = 38 + 17 * √5) :
    A^2 - A * ⌊A⌋ = 1 := by
  have h1 : ⌊A⌋ = 76 := by
    rw [hA]
    have h2 : (38 + 17 * Real.sqrt 5 : ℝ) ≥ (76 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h3 : (38 + 17 * Real.sqrt 5 : ℝ) < (77 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h4 : ⌊(38 + 17 * Real.sqrt 5 : ℝ)⌋ = 76 := by
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    exact h4
  rw [h1]
  rw [hA]
  have h5 : (38 + 17 * Real.sqrt 5 : ℝ) ^ 2 - (38 + 17 * Real.sqrt 5 : ℝ) * (76 : ℝ) = 1 := by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  exact_mod_cast h5