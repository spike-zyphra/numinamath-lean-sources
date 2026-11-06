import Mathlib

theorem algebra_98155 {a b c : ℝ} (ha : a ≠ 0) (h : ∃ x1 x2, x1 ≠ x2 ∧ a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0 ∧ x1 + x2 = x1 * x2) :
a + b + c = a := by
  rcases h with ⟨x1, x2, hx12, h1, h2, h3⟩
  have eq1 : a * (x1 + x2) + b = 0 := by
    have eq1 : a * x1 ^ 2 + b * x1 + c - (a * x2 ^ 2 + b * x2 + c) = 0 := by linarith
    have eq2 : a * (x1 ^ 2 - x2 ^ 2) + b * (x1 - x2) = 0 := by
      nlinarith
    have eq3 : (x1 - x2) * (a * (x1 + x2) + b) = 0 := by
      ring_nf at eq2 ⊢
      linarith
    cases' (mul_eq_zero.mp eq3) with h4 h5
    · -- h4 : x1 - x2 = 0
      exfalso
      apply hx12
      linarith
    · -- h5 : a * (x1 + x2) + b = 0
      linarith
  have eq2 : c = a * (x1 * x2) := by
    have h1 := h1
    rw [show b = -a * (x1 + x2) by linarith [eq1]] at h1
    nlinarith
  have eq5 : a * (x1 * x2) = a * (x1 + x2) := by
    have eq2' : x1 * x2 = x1 + x2 := by linarith [h3]
    rw [eq2']
  have eq6 : c = a * (x1 + x2) := by
    nlinarith [eq2, eq5]
  have eq7 : b = -a * (x1 + x2) := by
    linarith [eq1]
  nlinarith [eq6, eq7]