import Mathlib

theorem algebra_131485 {a b : ℝ} (ha : a ≠ b)
    (h1 : ∃ x, x^2 + a * x + b = 0 ∧ x^2 + b * x + a = 0) : a + b = -1 := by
  rcases h1 with ⟨x, hx1, hx2⟩
  have h_sub : (x^2 + a * x + b) - (x^2 + b * x + a) = 0 := by
    linarith
  have h_eq : (a - b) * x + (b - a) = 0 := by
    linarith [h_sub]
  have h_factor : (a - b) * (x - 1) = 0 := by
    linarith [h_eq]
  cases' (mul_eq_zero.mp h_factor) with h_a h_b
  · -- Case where a - b = 0, which would mean a = b, contradicting ha: a ≠ b
    exfalso
    exact ha (by linarith)
  · -- Case where x - 1 = 0, so x = 1
    have hx : x = 1 := by linarith
    rw [hx] at hx1
    nlinarith