import Mathlib

theorem algebra_248577 {a b x : ℝ} (h₀ : a ≠ b) (h₁ : a^3 - b^3 = 19 * x^3) (h₂ : a - b = x) :
    a = 3 * x ∨ a = -2 * x := by

  have h3 : x ≠ 0 := by
    by_contra h
    have h4 : a - b = 0 := by
      rw [h] at h₂
      linarith
    have h5 : a = b := by linarith
    contradiction
  
  have eq1 : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) := by ring
  rw [eq1] at h₁
  rw [h₂] at h₁
  
  have eq2 : a^2 + a * b + b^2 = 19 * x^2 := by
    apply (mul_left_inj' h3).mp
    linarith
  
  have h4 : b = a - x := by linarith
  
  rw [h4] at eq2
  
  have eq3 : 3 * a^2 - 3 * a * x - 18 * x^2 = 0 := by
    nlinarith
  
  have eq4 : a^2 - a * x - 6 * x^2 = 0 := by
    nlinarith
  
  have h5 : (a - 3 * x) * (a + 2 * x) = 0 := by
    nlinarith [eq4]

  cases' (mul_eq_zero.mp h5) with h6 h7
  · left
    linarith
  · right
    linarith