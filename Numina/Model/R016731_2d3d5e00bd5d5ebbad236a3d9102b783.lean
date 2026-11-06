import Mathlib

theorem algebra_4988 (a : ℝ) (ha : a > 2) (c : ℤ) (h : ∃ x : ℝ, a * x ^ 2 + 11 * x + 4 * c = 0) :
    c ≤ 3 := by
  rcases h with ⟨x, hx⟩
  have h1 : (2 * a * x + 11) ^ 2 = 121 - 16 * a * (c : ℝ) := by
    nlinarith [sq_nonneg (2 * a * x + 11), sq_nonneg (x)]
  have h2 : (121 - 16 * a * (c : ℝ)) ≥ 0 := by
    nlinarith [sq_nonneg (2 * a * x + 11), sq_nonneg (x)]
  by_contra h4
  push_neg at h4
  have h4' : c ≥ 4 := by omega
  have h5 : (c : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h4'
  nlinarith [h5, h2, mul_pos (show (0 : ℝ) < a - 2 by linarith) (show (0 : ℝ) < a - 2 by linarith)]