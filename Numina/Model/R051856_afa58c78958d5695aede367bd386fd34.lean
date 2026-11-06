import Mathlib

theorem algebra_285085 {x y z : ℝ} (h₀ : x * 3 = y * 2) (h₁ : y * 4 = z * 3)
    (h₂ : x^2 + y^2 + z^2 = 725) :
    (x = 10 ∧ y = 15 ∧ z = 20) ∨ (x = -10 ∧ y = -15 ∧ z = -20) := by
  have h3 : y = 3/2 * x := by
    linarith
  have h4 : z = 2 * x := by
    rw [h3] at h₁
    linarith
  rw [h3, h4] at h₂
  have h5 : x^2 = 100 := by
    nlinarith
  have h6 : x = 10 ∨ x = -10 := by
    have h7 : x^2 - 100 = 0 := by linarith
    have h8 : (x - 10) * (x + 10) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h8) with h9 h10
    · left
      linarith
    · right
      linarith
  cases h6 with
  | inl h7 =>
    have hy1 : y = 15 := by
      rw [show x = 10 by linarith] at h3
      linarith
    have hz1 : z = 20 := by
      rw [show x = 10 by linarith] at h4
      linarith
    left
    exact ⟨h7, hy1, hz1⟩
  | inr h7 =>
    have hy1 : y = -15 := by
      rw [show x = -10 by linarith] at h3
      linarith
    have hz1 : z = -20 := by
      rw [show x = -10 by linarith] at h4
      linarith
    right
    exact ⟨h7, hy1, hz1⟩