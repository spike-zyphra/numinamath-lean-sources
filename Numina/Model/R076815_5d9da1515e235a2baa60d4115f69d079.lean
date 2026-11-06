import Mathlib

theorem algebra_321557 (a b c d e : ℝ)
    (h₀ : a + b + c + d + e = 8) (h₁ : a^2 + b^2 + c^2 + d^2 + e^2 = 16) :
    0 ≤ e ∧ e ≤ 16 / 5 := by
  have h2 : a + b + c + d = 8 - e := by linarith
  have h4 : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a + b - c - d), sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b + c + d)]
  have h5 : (8 - e) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    rw [h2] at *
    nlinarith [h4]
  have h6 : a^2 + b^2 + c^2 + d^2 = 16 - e^2 := by linarith [h₁]
  rw [h6] at h5
  have h7 : 5 * e^2 - 16 * e ≤ 0 := by 
    nlinarith [h5]
  constructor
  · -- Proof that $0 \leq e$
    nlinarith [h7]
  · -- Proof that $e \leq 16 / 5$
    nlinarith [h7]