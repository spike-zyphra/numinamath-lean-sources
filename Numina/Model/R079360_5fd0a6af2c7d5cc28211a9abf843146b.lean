import Mathlib

theorem algebra_175699 (a b c : ℕ) (h₀ : a + b + c = 58) (h₁ : (3 / 4 : ℚ) * c = (2 / 3 : ℚ) * a)
    (h₂ : (3 / 4 : ℚ) * c = b / 2) :
    a = 18 ∧ b = 24 ∧ c = 16 := by
  have h₃ : (a : ℚ) + (b : ℚ) + (c : ℚ) = (58 : ℚ) := by exact_mod_cast h₀
  have eq2 : (8 : ℚ) * (a : ℚ) = (9 : ℚ) * (c : ℚ) := by
    linarith
  have eq3 : (2 : ℚ) * (b : ℚ) = (3 : ℚ) * (c : ℚ) := by
    linarith
  have hc : (c : ℚ) = 16 := by
    have h₄ : (a : ℚ) = (9 / 8 : ℚ) * (c : ℚ) := by 
      linarith [eq2]
    have h₅ : (b : ℚ) = (3 / 2 : ℚ) * (c : ℚ) := by
      linarith [eq3]
    rw [h₄, h₅] at h₃
    linarith
  have ha : (a : ℚ) = 18 := by 
    rw [hc] at eq2
    linarith
  have hb : (b : ℚ) = 24 := by 
    rw [hc] at eq3
    linarith
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hc⟩