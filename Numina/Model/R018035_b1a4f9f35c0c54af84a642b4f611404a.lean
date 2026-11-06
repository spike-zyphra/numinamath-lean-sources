import Mathlib

theorem algebra_114530 {x y z : ℝ} (h₀ : x ≠ y) (h₁ : y ≠ z) (h₂ : z ≠ x)
    (h₃ : x^2 + y^2 = -x + 3 * y + z) (h₄ : y^2 + z^2 = x + 3 * y - z) (h₅ : x^2 + z^2 = 2 * x + 2 * y - z) :
    (x = 0 ∧ y = 1 ∧ z = -2) ∨ (x = -3 / 2 ∧ y = 5 / 2 ∧ z = -1 / 2) := by

  have h6 : (x - y) * (x + y - 1) = 0 := by
    nlinarith

  cases (mul_eq_zero.1 h6) with
  | inl h7 =>
    have h8 : x = y := by linarith
    exfalso
    apply h₀
    linarith
  | inr h7 =>
    have h77 : x + y = 1 := by linarith
    have h8 : y = 1 - x := by
      linarith
    have h777 : (x - z) * (x + z + 2) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by
        intro h
        apply h₀
        linarith
      ), sq_pos_of_ne_zero (show (y - z) ≠ 0 by
        intro h
        apply h₁
        linarith
      ), sq_pos_of_ne_zero (show (z - x) ≠ 0 by
        intro h
        apply h₂
        linarith
      ) ]
    cases (mul_eq_zero.1 h777) with
    | inl h55 =>
      have h99 : x = z := by linarith
      exfalso
      apply h₂
      linarith
    | inr h66 =>
      have h9 : z = -x - 2 := by
        linarith
      rw [h8] at h₃
      rw [h9] at h₃
      have h11 : x * (2 * x + 3) = 0 := by
        nlinarith
      cases (mul_eq_zero.1 h11) with
      | inl h12 =>
        left
        constructor
        · -- x = 0
          linarith
        constructor
        · -- y = 1
          nlinarith
        · -- z = -2
          nlinarith
      | inr h13 =>
        right
        constructor
        · -- x = -3/2
          linarith
        constructor
        · -- y = 5/2
          nlinarith
        · -- z = -1/2
          nlinarith