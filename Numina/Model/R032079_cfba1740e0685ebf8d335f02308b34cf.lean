import Mathlib

theorem number_theory_23496 (A B C : ℕ) (h₀ : A ≠ B) (h₁ : A ≠ C) (h₂ : B ≠ C)
    (h₃ : 1 ≤ A ∧ A ≤ 9) (h₄ : 1 ≤ B ∧ B ≤ 9) (h₅ : 1 ≤ C ∧ C ≤ 9)
    (h₆ : A + B = C) (h₇ : 10 * A + A - B = 2 * C) (h₈ : C * B = 10 * A + A + A) :
    A + B + C = 8 := by
  have h6 : A + B = C := h₆
  have h7 : 11 * A - B = 2 * C := by
    omega
  have h8 : C * B = 12 * A := by
    nlinarith
  -- Derive B and C in terms of A
  have h9 : B = 3 * A := by
    omega
  -- Derive C in terms of A
  have h10 : C = 4 * A := by
    omega
  -- Substitute into the third equation
  rw [show B = 3 * A by linarith, show C = 4 * A by linarith] at h8
  -- Solve for A
  have h12 : A = 1 := by
    nlinarith
  -- Solve for B and C
  have h14 : B = 3 := by
    nlinarith
  have h15 : C = 4 := by
    nlinarith
  -- Prove the final sum
  linarith [h12, h14, h15]