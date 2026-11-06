import Mathlib

  theorem algebra_197789 {a b : ℕ} (ha : a > 0) (hb : b > 0) (hab : a > b)
  (h₀ : (4 * a : ℤ) - (4 * b : ℤ) = 24) (h₁ : a * 2 = b * 3) :
  a^2 = 324 ∧ b^2 = 144 := by 
  have h2 : (a : ℤ) - (b : ℤ) = 6 := by
    linarith
  have h3 : (a : ℤ) = 18 := by
    omega
  have h4 : (b : ℤ) = 12 := by
    omega
  have ha' : a = 18 := by
    norm_num at h3
    exact_mod_cast h3
  have hb' : b = 12 := by
    norm_num at h4
    exact_mod_cast h4
  constructor
  · -- Show a^2 = 324
    calc 
      a^2 = 18^2 := by rw [ha']
      _ = 324 := by norm_num
  · -- Show b^2 = 144
    calc 
      b^2 = 12^2 := by rw [hb']
      _ = 144 := by norm_num