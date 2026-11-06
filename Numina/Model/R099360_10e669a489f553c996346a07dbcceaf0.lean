import Mathlib

theorem algebra_302191 {k : ℝ} (h : ∃ x1 x2, x1 ≠ x2 ∧ x1^2 + k * x1 + k + 1 = 0 ∧ x2^2 + k * x2 + k + 1 = 0 ∧ x1 + 2 * x2^2 = k) :
    k = 5 := by
  rcases h with ⟨x1, x2, h12, h1, h2, h3⟩
  have eq1 : x1 + x2 = -k := by
    have h_eq : x1^2 + k * x1 + k + 1 - (x2^2 + k * x2 + k + 1) = 0 := by linarith
    have h_diff : (x1 - x2) * (x1 + x2 + k) = 0 := by
      ring_nf at h_eq ⊢
      nlinarith
    cases (mul_eq_zero.mp h_diff) with
    | inl h4 =>
      exfalso
      exact h12 (by linarith)
    | inr h5 =>
      linarith
  have eq2 : k = x2^2 - (x2)/2 := by
    have h4 : x1 = -k - x2 := by linarith
    rw [h4] at h3
    nlinarith
  have eq3 : x2^2 + k * x2 + k + 1 = 0 := h2
  rw [eq2] at eq3
  have h4 : 2 * x2^3 + 3 * x2^2 - x2 + 2 = 0 := by
    nlinarith
  have h5 : (x2 + 2) * (2 * x2^2 - x2 + 1) = 0 := by
    nlinarith [h4]
  cases (mul_eq_zero.mp h5) with
  | inl h6 =>
    have h2_val : x2 = -2 := by linarith
    rw [h2_val] at eq2
    nlinarith
  | inr h7 =>
    have h8 : 2 * x2^2 - x2 + 1 > 0 := by
      nlinarith [sq_nonneg (x2), sq_nonneg (x2 - 1 / 4)]
    nlinarith