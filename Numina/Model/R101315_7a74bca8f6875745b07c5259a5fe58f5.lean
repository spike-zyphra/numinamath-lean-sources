import Mathlib

open Real

theorem inequalities_277275 (k c : ℝ) (hk : ∃ a b, a > 0 ∧ b > 0 ∧ a^2 + b^2 = (c^2) ∧ k = a + b)
    (hc : c > 0) :
    sqrt 2 / 2 * k ≤ c := by
  rcases hk with ⟨a, b, ha, hb, h1, hk_eq⟩
  have h2 : k = a + b := by linarith
  have h3 : (a + b) ^ 2 ≤ 2 * (c ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have h4 : sqrt 2 / 2 * k ≤ c := by
    rw [show k = a + b by linarith]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith), sq_nonneg (sqrt 2 * (a + b) / 2 - c)]
  linarith [h4, show k = a + b by linarith]