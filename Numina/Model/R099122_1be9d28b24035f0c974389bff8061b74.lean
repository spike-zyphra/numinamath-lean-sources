import Mathlib

theorem algebra_20291 (a b c d : ℕ)
    (h₀ : a + b + c + d = 100)
    (h₁ : a = 3 * d)
    (h₂ : c = b + 10)
    (h₃ : (a / 100 : ℝ) + (c / 100 : ℝ) = 65 / 100) :
    a / 100 = 30 / 100 := by
  have h₄ : (a : ℝ) + (b : ℝ) + (c : ℝ) + (d : ℝ) = (100 : ℝ) := by exact_mod_cast h₀
  have h₅ : (a : ℝ) = 3 * (d : ℝ) := by exact_mod_cast h₁
  have h₆ : (c : ℝ) = (b : ℝ) + (10 : ℝ) := by exact_mod_cast h₂
  have h₇ : (a : ℝ) + (c : ℝ) = (65 : ℝ) := by
    have h₈ : (a : ℝ) / 100 + (c : ℝ) / 100 = (65 : ℝ) / 100 := by
      linarith [h₃]
    have h₉ : (a : ℝ) + (c : ℝ) = (65 : ℝ) := by
      linarith
    linarith
  rw [h₅, h₆] at h₄ h₇
  have hd : (d : ℝ) = (10 : ℝ) := by 
    linarith
  have ha : (a : ℝ) = (30 : ℝ) := by 
    rw [hd] at h₅
    linarith
  have ha_nat : a = 30 := by 
    exact_mod_cast ha
  norm_num [ha_nat]