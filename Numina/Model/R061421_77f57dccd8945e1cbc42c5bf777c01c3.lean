import Mathlib

theorem algebra_209441 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b^2 + c^2 = b + a^2 + c^2 ∧ b + a^2 + c^2 = c + a^2 + b^2) :
    a = b ∨ b = c ∨ a = c := by
  have h₁ : a + b^2 + c^2 = b + a^2 + c^2 := h.1
  have h₂ : b + a^2 + c^2 = c + a^2 + b^2 := h.2

  have eq1 : (a - b) * (1 - (a + b)) = 0 := by
    nlinarith
  
  have eq2 : (b - c) * (1 - (b + c)) = 0 := by
    nlinarith
  
  cases' (mul_eq_zero.mp eq1) with h₃ h₄

  · -- Case where a - b = 0, so a = b
    left
    linarith
  
  · -- Case where 1 - (a + b) = 0, i.e., a + b = 1
    have hab : a + b = 1 := by linarith
  
    cases' (mul_eq_zero.mp eq2) with h₅ h₆

    · -- Subcase where b - c = 0, so b = c
      right
      left
      linarith
  
    · -- Subcase where 1 - (b + c) = 0, i.e., b + c = 1
      have hbc : b + c = 1 := by linarith
      have hac : a = c := by
        nlinarith [hab, hbc]
      right
      right
      linarith