import Mathlib

theorem algebra_110015 {a b c d : ℤ} (h₀ : a + b + c + d = 45) (h₁ : a + 2 = b - 2)
    (h₂ : b - 2 = 2 * c) (h₃ : 2 * c = d / 2) :
    a = 8 ∧ b = 12 ∧ c = 5 ∧ d = 20 := by
  have h4 : a = b - 4 := by
    linarith
  have h5 : b = 2 * c + 2 := by
    linarith
  have h6 : d = 4 * c := by
    omega
  have h7 : c = 5 := by
    rw [show a = 2 * c - 2 by linarith [h4, h5]] at h₀
    rw [show b = 2 * c + 2 by linarith [h5]] at h₀
    rw [show d = 4 * c by linarith [h6]] at h₀
    omega
  have ha : a = 8 := by 
    linarith [h7, h4, h5]
  have hb : b = 12 := by 
    linarith [h7, h5]
  have hd : d = 20 := by 
    linarith [h7, h6]
  exact ⟨ha, hb, h7, hd⟩