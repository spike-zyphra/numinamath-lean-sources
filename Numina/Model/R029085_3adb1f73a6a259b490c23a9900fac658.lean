import Mathlib

theorem algebra_600325 (a b c d e : ℝ)
    (h₀ : a + b + c + d + e = 8) (h₁ : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 16) :
    0 ≤ e ∧ e ≤ 16 / 5 := by
  have h2 : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by 
    nlinarith [sq_nonneg (a + b + c + d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  have eq1 : a + b + c + d = 8 - e := by linarith
  have eq2 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 16 - e ^ 2 := by linarith
  rw [eq1, eq2] at h2
  constructor
  · -- Prove 0 ≤ e
    nlinarith
  · -- Prove e ≤ 16/5
    nlinarith