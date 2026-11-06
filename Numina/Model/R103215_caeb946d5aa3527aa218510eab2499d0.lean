import Mathlib

theorem algebra_135546 {a b : ℝ} (ha : a ≠ b) (h1 : ∃ x, x^2 + a * x + 3 * b = 0 ∧ x^2 + b * x + 3 * a = 0) :
    a + b = -3 := by
  rcases h1 with ⟨x, hx1, hx2⟩
  have h_sub : (a - b) * x + 3 * (b - a) = 0 := by
    linarith
  have h_eq : (a - b) * (x - 3) = 0 := by
    linarith
  
  cases' (mul_eq_zero.mp h_eq) with h_a_b h_x_3
  · 
    exfalso
    exact ha (by linarith)
  · 
    have hx_eq : x = 3 := by linarith
    rw [hx_eq] at hx1
    linarith