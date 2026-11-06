import Mathlib

theorem algebra_15177 (a b c x y z : ℝ) (h₀ : 13 * x + b * y + c * z = 0)
    (h₁ : a * x + 23 * y + c * z = 0) (h₂ : a * x + b * y + 42 * z = 0)
    (h₃ : a ≠ 13) (h₄ : x ≠ 0) :
    a / (a - 13) + b / (b - 23) + c / (c - 42) = 1 := by
  have eq1 : (a - 13) * x = (b - 23) * y := by
    nlinarith
  have eq2 : (b - 23) * y = (c - 42) * z := by
    nlinarith
  have h5 : b - 23 ≠ 0 := by
    by_contra h
    have : b = 23 := by linarith
    rw [show b = 23 by linarith] at eq1 eq2
    have eq6 : (a - 13) * x = 0 := by
      nlinarith
    have eq7 : a - 13 = 0 := by
      apply (mul_right_inj' h₄).mp
      linarith
    have eq8 : a = 13 := by linarith
    contradiction
  have h6 : c - 42 ≠ 0 := by
    by_contra h
    have : c = 42 := by linarith
    rw [show c = 42 by linarith] at eq2
    have eq7 : (b - 23) * y = 0 := by
      nlinarith
    have eq8 : y = 0 := by
      apply (mul_left_inj' h5).mp
      linarith
    have eq9 : (a - 13) * x = 0 := by
      nlinarith [eq8]
    have eq10 : a - 13 = 0 := by
      apply (mul_right_inj' h₄).mp
      linarith
    have eq11 : a = 13 := by linarith
    contradiction
  have h7 : a - 13 ≠ 0 := by
    intro h
    apply h₃
    linarith
  have eq11 : 13 + b * ((a - 13) / (b - 23)) + c * ((a - 13) / (c - 42)) = 0 := by
    have eq8 : y = ((a - 13) / (b - 23)) * x := by
      have eq9 : (a - 13) * x = (b - 23) * y := eq1
      field_simp [show b - 23 ≠ 0 by exact h5] at eq9 ⊢
      linarith
    have eq9 : z = ((a - 13) / (c - 42)) * x := by
      have eq10 : (b - 23) * y = (c - 42) * z := eq2
      rw [eq8] at eq10
      field_simp [show c - 42 ≠ 0 by exact h6] at eq10 ⊢
      nlinarith
    have eq10 : 13 * x + b * y + c * z = 0 := h₀
    rw [eq8, eq9] at h₀
    have : x ≠ 0 := h₄
    have eq13 : 13 + b * ((a - 13) / (b - 23)) + c * ((a - 13) / (c - 42)) = 0 := by
      apply (mul_left_inj' h₄).mp
      field_simp [show b - 23 ≠ 0 by exact h5, show c - 42 ≠ 0 by exact h6] at h₀ ⊢
      nlinarith
    linarith
  field_simp [show a - 13 ≠ 0 by exact h7, show b - 23 ≠ 0 by exact h5, show c - 42 ≠ 0 by exact h6] at eq11 ⊢
  nlinarith [eq11, sq_pos_of_ne_zero (show (a - 13 : ℝ) ≠ 0 by exact h7), sq_pos_of_ne_zero (show (b - 23 : ℝ) ≠ 0 by exact h5), sq_pos_of_ne_zero (show (c - 42 : ℝ) ≠ 0 by exact h6)]