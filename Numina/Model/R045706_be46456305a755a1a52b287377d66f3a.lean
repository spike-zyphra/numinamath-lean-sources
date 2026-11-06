import Mathlib

open Real
open scoped BigOperators

theorem inequalities_597548 {p : ℝ} (hp : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 →
  (1 / (a ^ 2 + b ^ 2) ^ (1 / 2) + 1 / (b ^ 2 + c ^ 2) ^ (1 / 2)) ≥
  p * (1 / a + 1 / b)) :
  p ≤ 1 + sqrt 2 := by
  have h1 := hp 1 1 (Real.sqrt 2)
    (by norm_num) (by norm_num) (by positivity)
  have h2 : ( (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
    norm_num
  have h2' : ( (1 : ℝ) ^ 2 + (Real.sqrt 2 : ℝ) ^ 2) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ (1 / 2 : ℝ) := by
    have h3 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [h3]
    norm_num
  norm_num [h2, h2'] at h1
  -- All terms are positive, use `linarith`.
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 2 - 1),
    Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0),
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (2 : ℝ) ≥ 0),
    Real.sqrt_nonneg 2
  ]