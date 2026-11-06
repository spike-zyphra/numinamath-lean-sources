import Mathlib

theorem algebra_274583 (P Q R S : ℝ) (h₀ : 0 < P ∧ P < Q ∧ Q < R ∧ R < S)
    (h₁ : Q - P = 1) (h₂ : R - Q = 2 * (Q - P)) (h₃ : S - R = 3 * (R - Q)) :
    S - P = 9 := by
  have h4 : Q - P = 1 := h₁
  have h5 : R - Q = 2 := by
    rw [show Q - P = 1 by linarith] at h₂
    linarith
  have h6 : S - R = 6 := by
    rw [show R - Q = 2 by linarith [h5]] at h₃
    linarith
  have h7 : S - P = (S - R) + (R - Q) + (Q - P) := by
    ring
  rw [h7]
  rw [h6, h5, h4]
  all_goals linarith