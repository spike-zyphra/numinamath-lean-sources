import Mathlib

theorem algebra_187422 {a : ℝ} (h : ∃ x1 x2, x1 ≠ x2 ∧ x1^2 - (2 * a + 1) * x1 + a^2 + 2 = 0 ∧
    x2^2 - (2 * a + 1) * x2 + a^2 + 2 = 0 ∧ x1 = 2 * x2) :
    a = 4 := by 
  obtain ⟨x1, x2, h12, h1, h2, h21⟩ := h
  have h3 : x1 = 2 * x2 := h21
  rw [h3] at h1 
  have eq1 : 3 * x2^2 - (2 * a + 1) * x2 = 0 := by 
    nlinarith 
  have h4 : x2 * (3 * x2 - (2 * a + 1)) = 0 := by 
    nlinarith 
  cases (mul_eq_zero.mp h4) with 
  | inl h5 =>
    have h6 : x2 = 0 := h5 
    have h7 : x1 = 0 := by 
      linarith [h3, h6] 
    exfalso 
    exact h12 (by linarith) 
  | inr h8 =>
    have h9 : 3 * x2 = 2 * a + 1 := by linarith 
    have h10 : x2 = (2 * a + 1) / 3 := by 
      linarith 
    rw [h10] at h2 
    nlinarith [sq_nonneg (a - 4)]