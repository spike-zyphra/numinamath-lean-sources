import Mathlib

theorem algebra_6576 {x : ℝ} (hx : x > 0)  (h : x ^ 3 + 1 / x ^ 3 = 2) :
    x + 1 / x = 2 := by
  have h1 : x > 0 := hx
  have h2 : x + 1 / x > 0 := by
    have hx1 : x > 0 := h1
    have hx2 : 1 / x > 0 := by positivity
    linarith
  have eq1 : (x + 1 / x) ^ 3 = x^3 + 1 / x^3 + 3 * (x + 1 / x) := by
    field_simp [pow_three]
    <;> ring
  rw [h] at eq1
  have eq2 : (x + 1 / x) ^ 3 - 3 * (x + 1 / x) - 2 = 0 := by 
    linarith [eq1]
  have eq3 : (x + 1 / x - 2) * ((x + 1 / x) ^ 2 + 2 * (x + 1 / x) + 1) = 0 := by
    ring_nf at eq2 ⊢
    <;> nlinarith
  cases' (mul_eq_zero.mp eq3) with h4 h5
  · 
    have h6 : x + 1 / x = 2 := by
      linarith
    exact h6
  · 
    have h7 : (x + 1 / x) ^ 2 + 2 * (x + 1 / x) + 1 = 0 := by
      linarith
    have h8 : (x + 1 / x + 1) ^ 2 = 0 := by
      nlinarith
    have h9 : x + 1 / x + 1 = 0 := by
      nlinarith [sq_nonneg (x + 1 / x + 1)]
    have h10 : x + 1 / x = -1 := by linarith
    nlinarith [h10, h2]