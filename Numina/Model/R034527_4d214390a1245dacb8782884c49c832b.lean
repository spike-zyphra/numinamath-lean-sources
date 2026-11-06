import Mathlib

open Real

theorem algebra_96549 {S : ℝ → ℝ} {a : ℝ} (ha : -1 < a ∧ a < 1)
(hS : ∀ r, S r = ∑' n : ℕ, 12 * r ^ n) (h : S a * S (-a) = 2016):
S a + S (-a) = 336 := by
  have h1 : S a = 12 / (1 - a) := by 
    rw [hS a]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · -- Show that |a| < 1
      have h2 : abs a < 1 := by
        rw [abs_lt]
        constructor <;> linarith [ha.1, ha.2]
      simpa using h2

  have h3 : S (-a) = 12 / (1 + a) := by
    rw [hS (-a)]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · -- Show that |-a| < 1
      have h4 : abs (-a) < 1 := by
        rw [abs_neg, abs_lt]
        constructor <;> linarith [ha.1, ha.2]
      simpa using h4

  rw [h1, h3] at h 
  have h4 : 1 - a ^ 2 = 1 / 14 := by
    field_simp [(show (1 - a : ℝ) ≠ 0 by nlinarith), (show (1 + a : ℝ) ≠ 0 by nlinarith)] at h ⊢
    nlinarith
  
  have h5 : S a + S (-a) = 24 / (1 - a ^ 2) := by
    rw [h1, h3]
    have denom : (1 - a : ℝ) * (1 + a : ℝ) = 1 - a ^ 2 := by 
      nlinarith
    field_simp [(show (1 - a : ℝ) ≠ 0 by nlinarith), (show (1 + a : ℝ) ≠ 0 by nlinarith), denom]
    <;> nlinarith

  rw [h5, h4]
  norm_num