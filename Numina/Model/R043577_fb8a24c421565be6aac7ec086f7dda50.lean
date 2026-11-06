import Mathlib

theorem algebra_114278 (a b c : ℝ) (h₀ : a^2 + b = c^2) (h₁ : b^2 + c = a^2)
    (h₂ : c^2 + a = b^2) :
    (a, b, c) = (0, 0, 0) ∨ (a, b, c) = (0, 1, -1) ∨ (a, b, c) = (-1, 0, 1) ∨
    (a, b, c) = (1, -1, 0) := by

  have h3 : a + b + c = 0 := by
    nlinarith

  have h4 : c = -a - b := by 
    linarith

  rw [h4] at h₀ h₁ h₂

  have h5 : a * (a + 2 * b + 1) = 0 := by 
    nlinarith
  
  cases (mul_eq_zero.mp h5) with
  | inl ha0 =>
    have ha0' : a = 0 := by
      linarith

    have h6 : b * (b - 1) = 0 := by 
      rw [ha0'] at h₀
      nlinarith

    cases (mul_eq_zero.mp h6) with 
    | inl hb0 =>
      have hb0' : b = 0 := by
        linarith

      have hc0 : c = 0 := by
        nlinarith [h4, ha0', hb0']

      left
      simp [ha0', hb0', hc0]

    | inr hb1 =>
      have hb1' : b = 1 := by 
        linarith

      have hc1 : c = -1 := by 
        nlinarith [h4, ha0', hb1']

      right
      left
      simp [ha0', hb1', hc1]

  | inr ha2b =>
    have h8 : b * (b + 1) = 0 := by 
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]

    cases (mul_eq_zero.mp h8) with
    | inl hb0 =>
      have hb0' : b = 0 := by 
        linarith

      have ha1' : a = -1 := by 
        nlinarith

      have hc1' : c = 1 := by 
        nlinarith [h4, ha1', hb0']

      right
      right
      left
      simp [ha1', hb0', hc1']

    | inr hb1 =>
      have hb1' : b = -1 := by 
        linarith

      have ha1' : a = 1 := by 
        nlinarith

      have hc0' : c = 0 := by 
        nlinarith [h4, ha1', hb1']

      right
      right
      right
      simp [ha1', hb1', hc0']