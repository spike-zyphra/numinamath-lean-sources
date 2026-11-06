import Mathlib

theorem algebra_165065 (a b c d : ℤ) :
    a^2 - b^2 - c^2 - d^2 = c - b - 2 ∧
    2 * a * b = a - d - 32 ∧
    2 * a * c = 28 - a - d ∧
    2 * a * d = b + c + 31 ↔ (a, b, c, d) = (5, -3, 2, 3) := by
  constructor
  · -- Forward direction: proving that the equations imply (5, -3, 2, 3).
    rintro ⟨h₁, h₂, h₃, h₄⟩
    have h₅ : (a - 5) * (a + 5) = 0 := by
      nlinarith [sq_nonneg (a - 5), sq_nonneg (b + 3), sq_nonneg (c - 2), sq_nonneg (d - 3)]
    have ha1 : a = 5 ∨ a = -5 := by
      cases (mul_eq_zero.mp h₅) with
      | inl h =>
        left
        linarith
      | inr h =>
        right
        linarith
    rcases ha1 with ha | ha
    ·
      have ha2 : a = 5 := ha
      rw [ha2] at h₂ h₃ h₄
      have h6 : b = -3 := by
        omega
      have h7 : c = 2 := by
        omega
      have h8 : d = 3 := by
        omega
      simp [ha2, h6, h7, h8]
    ·
      have ha2 : a = -5 := by linarith
      rw [ha2] at h₂ h₃ h₄
      exfalso
      omega
  · -- Backward direction: proving that (5, -3, 2, 3) satisfies the equations.
    rintro ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · -- First equation
      norm_num
    constructor
    · -- Second equation
      norm_num
    constructor
    · -- Third equation
      norm_num
    · -- Fourth equation
      norm_num