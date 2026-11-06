import Mathlib

theorem algebra_618821 {r s : ℝ} {P : ℝ → ℝ} (hp : P = fun x => x ^ 2 + r * x + s)
    (hroots : ∃ x y, x ≠ y ∧ x < -1 ∧ y < -1 ∧ P x = 0 ∧ P y = 0 ∧ |x - y| < 2) :
    ∀ x, P (P x) > 0 := by
  rcases hroots with ⟨x, y, hxy, hx1, hy1, hPx, hPy, hxy2⟩
  have eq1 : x^2 + r * x + s = 0 := by
    rw [hp] at hPx
    simpa using hPx
  have eq2 : y^2 + r * y + s = 0 := by
    rw [hp] at hPy
    simpa using hPy
  have h_sum : x + y = -r := by
    have h : x^2 + r * x + s - (y^2 + r * y + s) = 0 := by linarith
    have h' : (x - y) * (x + y + r) = 0 := by
      ring_nf at h ⊢
      linarith
    cases' (mul_eq_zero.mp h') with h1 h2
    · -- x - y = 0, but x ≠ y
      exfalso
      exact hxy (by linarith)
    · -- x + y + r = 0
      linarith
  have h_prod : x * y = s := by
    nlinarith [sq_nonneg (x - y), eq1, eq2, h_sum]
  have h6 : (x - y) ^ 2 < 4 := by
    rw [abs_lt] at hxy2
    nlinarith
  have h_diff_sq : (x - y) ^ 2 = r ^ 2 - 4 * s := by
    nlinarith [sq_nonneg (x - y), eq1, eq2, h_sum, h_prod]
  have h_pos : ∀ x, P x > -1 := by
    intro x
    have hx1 : P x = x ^ 2 + r * x + s := by
      rw [hp]
    rw [hx1]
    nlinarith [sq_nonneg (x + r / 2), sq_nonneg (x - -1), h6, h_diff_sq, 
      mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 2 by norm_num)]
  intro x
  have hx1 : P (P x) > 0 := by
    have h1 : P (P x) = (P x) ^ 2 + r * (P x) + s := by
      rw [hp]
    rw [h1]
    have hx2 : P x > -1 := h_pos x
    nlinarith [sq_nonneg (P x + r / 2), sq_nonneg (P x - -1), h6, h_diff_sq, 
      mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 2 by norm_num)]
  linarith [hx1]