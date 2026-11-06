import Mathlib

theorem algebra_189862 (a b c d : ℕ) (h₀ : a + b + c + d = 25)
    (h₁ : a > b) (h₂ : b > c) (h₃ : c > d)
    (h₄ : a = b + c) (h₅ : b = c + d) :
    a = 11 ∧ b = 7 ∧ c = 4 ∧ d = 3 := by
  have h6 : a + b + c + d = 25 := h₀
  have ha : a = b + c := h₄
  have hb : b = c + d := h₅

  rw [ha] at h6 -- substitute a = b + c in the total equation
  rw [hb] at h6 -- substitute b = c + d into the equation

  -- Now h6 is 4 * c + 3 * d = 25
  have h_eq : 4 * c + 3 * d = 25 := by 
    omega

  -- From hb: b = c + d and h₂: b > c, we have c + d > c, so d > 0
  have h7 : d > 0 := by
    by_contra h
    push_neg at h
    have h8 : d = 0 := by linarith
    have h9 : b = c := by
      rw [hb]
      omega
    linarith

  have h9 : c = 4 := by 
    omega

  have h10 : d = 3 := by 
    rw [show c = 4 by omega] at h_eq
    omega

  have hb_val : b = 7 := by 
    rw [show c = 4 by omega, show d = 3 by omega] at hb
    omega

  have ha_val : a = 11 := by 
    rw [show b = 7 by omega, show c = 4 by omega] at ha
    omega
  
  exact ⟨ha_val, hb_val, show c = 4 by omega, show d = 3 by omega⟩