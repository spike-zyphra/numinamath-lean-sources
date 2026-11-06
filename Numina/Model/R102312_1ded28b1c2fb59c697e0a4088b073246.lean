import Mathlib

theorem algebra_13369 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h₀ : a^2 + b^2 = 65) (h₁ : a^2 - b^2 = 33) :
    4 * (a + b) = 44 := by 
  have h2 : a^2 = 49 := by 
    omega
  have ha2 : a = 7 := by 
    nlinarith
  have h3 : b^2 = 16 := by 
    nlinarith [h₀, h2]
  have hb2 : b = 4 := by 
    nlinarith
  calc
    4 * (a + b) = 4 * (7 + 4) := by rw [ha2, hb2]
    _ = 4 * 11 := by norm_num
    _ = 44 := by norm_num