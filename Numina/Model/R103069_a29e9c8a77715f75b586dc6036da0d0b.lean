import Mathlib

theorem algebra_1201 {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
(h : (13 / 15 : ℚ) = a / 3 + b / 5) : a = 2 ∧ b = 1 := by
   have h1 : (a : ℚ) > (0 : ℚ) := by exact_mod_cast ha
   have h2 : (b : ℚ) > (0 : ℚ) := by exact_mod_cast hb
   have h3 : 13 = 5 * (a : ℚ) + 3 * (b : ℚ) := by
     field_simp at h ⊢
     nlinarith -- Solving linear and nonlinear goals using nlinarith
   have h4 : 13 = 5 * a + 3 * b := by
     exact_mod_cast h3
   have h5 : a > 0 := by omega -- automatically deduces positivity of a
   have h6 : b > 0 := by omega -- automatically deduces positivity of b
   have h7 : a ≤ 2 := by 
     omega
   have h8 : a = 2 := by 
     omega
   have h9 : b = 1 := by 
     omega
   exact ⟨h8, h9⟩