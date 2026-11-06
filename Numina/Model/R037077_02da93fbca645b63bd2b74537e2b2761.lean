import Mathlib

theorem algebra_114579 (a b c : ℝ) :
    a * (b ^ 2 + c) = c * (c + a * b) ∧ b * (c ^ 2 + a) = a * (a + b * c) ∧
    c * (a ^ 2 + b) = b * (b + a * c) ↔ a = b ∧ b = c := by
  constructor
  · -- Assume the three equations hold, prove a = b ∧ b = c
    rintro ⟨h1, h2, h3⟩
    have eq1 : (a - b) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have h4 : a - b = 0 := by
      rw [sq_eq_zero_iff] at eq1
      linarith
    have eq2 : (b - c) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have h5 : b - c = 0 := by
      rw [sq_eq_zero_iff] at eq2
      linarith
    constructor
    · -- a = b
      linarith
    · -- b = c
      linarith
  · -- Assume a = b ∧ b = c, prove the three equations
    rintro ⟨r1, r2⟩
    have ha1 : a = b := by linarith
    have ha2 : b = c := by linarith
    constructor
    · -- First equation
      have ha3 : c = a := by linarith
      rw [show b = a by linarith, show c = a by linarith]
      nlinarith
    constructor
    · -- Second equation
      have ha3 : c = a := by linarith
      rw [show c = a by linarith, show b = a by linarith]
      nlinarith
    · -- Third equation
      have ha3 : c = a := by linarith
      rw [show c = a by linarith, show b = a by linarith]
      nlinarith