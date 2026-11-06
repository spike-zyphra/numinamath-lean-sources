import Mathlib

theorem algebra_209900 {A B C : ℝ} (h1 : 1 + A + B = A * B) (h2 : 2 + A + C = A * C)
    (h3 : 5 + B + C = B * C) :
    (A = 2 ∧ B = 3 ∧ C = 4) ∨ (A = 0 ∧ B = -1 ∧ C = -2) := by

  have eq1 : (A - 1) * (B - 1) = 2 := by
    nlinarith

  have eq2 : (A - 1) * (C - 1) = 3 := by
    nlinarith

  have eq3 : (B - 1) * (C - 1) = 6 := by
    nlinarith

  -- Solving the algebraic system by getting (A-1)^2 = 1.
  have h4 : (A - 1) ^ 2 = 1 := by
    nlinarith [sq_nonneg (A - 1), sq_nonneg (B - 1), sq_nonneg (C - 1)]

  have h5 : A - 1 = 1 ∨ A - 1 = -1 := by
    rw [sq_eq_one_iff] at h4
    exact h4

  cases h5 with
  | inl h6 =>
    have ha1 : A = 2 := by linarith
    have hb1 : B = 3 := by
      rw [show A = 2 by linarith] at eq1
      nlinarith
    have hc1 : C = 4 := by
      rw [show A = 2 by linarith] at eq2
      nlinarith
    left
    exact ⟨ha1, hb1, hc1⟩
  | inr h7 =>
    have ha2 : A = 0 := by linarith
    have hb2 : B = -1 := by
      rw [show A = 0 by linarith] at eq1
      nlinarith
    have hc2 : C = -2 := by
      rw [show A = 0 by linarith] at eq2
      nlinarith
    right
    exact ⟨ha2, hb2, hc2⟩