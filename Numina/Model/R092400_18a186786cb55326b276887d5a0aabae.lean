import Mathlib

theorem algebra_104269 (a b c d : ℕ) (h₀ : a + b + c + d = 55) (h₁ : a = b / 2)
    (h₂ : c = (a + b) / 2) (h₃ : d = 2 * (b - c)) :
    a = 10 ∧ b = 20 ∧ c = 15 ∧ d = 10 := by 
  have h4 : b = 2 * a := by 
    omega
  have h5 : c = (3 * a) / 2 := by 
    rw [show b = 2 * a by omega] at h₂
    omega
  have h6 : d = a := by 
    rw [show b = 2 * a by omega] at h₃
    rw [show c = (3 * a) / 2 by omega] at h₃
    omega
  have h7 : 11 * a = 110 := by 
    omega
  have ha : a = 10 := by 
    omega
  have hb : b = 20 := by 
    omega
  have hc : c = 15 := by 
    omega
  have hd : d = 10 := by 
    omega
  exact ⟨ha, hb, hc, hd⟩