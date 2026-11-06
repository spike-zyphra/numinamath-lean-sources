import Mathlib

theorem algebra_163176 (a b c d : ℕ) (h₀ : a + b + c + d = 900)
    (h₁ : a = (1 / 3 : ℚ) * 900) (h₂ : b = (1 / 4 : ℚ) * (900 - a))
    (h₃ : c = d) :
    a = 300 ∧ b = 150 ∧ c = 225 ∧ d = 225 ∧
    (a * 250 + b * 250 + c * 250 + d * 250) = 225000 := by
  have ha : (a : ℚ) = 300 := by
    norm_num at h₁ 
    exact h₁
  have ha_nat : a = 300 := by 
    exact_mod_cast ha 
  have hb : (b : ℚ) = 150 := by 
    rw [ha_nat] at h₂ 
    norm_num at h₂ ⊢
    exact h₂ 
  have hb_nat : b = 150 := by 
    exact_mod_cast hb 
  have h₄ : c + d = 450 := by 
    omega 
  have hc : c = 225 := by 
    omega 
  have hd : d = 225 := by 
    omega 
  have h_total : (a * 250 + b * 250 + c * 250 + d * 250) = 225000 := by 
    omega 
  exact ⟨ha_nat, hb_nat, hc, hd, h_total⟩