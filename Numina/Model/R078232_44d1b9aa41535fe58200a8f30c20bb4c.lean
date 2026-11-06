import Mathlib

theorem algebra_181602 (a b c : ℕ) (ha : a + 55 = b + c) (hb : b + 33 = a + c)
    (hc : a < (1 / 4 : ℚ) * c) :
    a + b + c ≤ 75 := by
  have h1 : (a : ℚ) + 55 = (b : ℚ) + (c : ℚ) := by
    exact_mod_cast ha
  have h2 : (b : ℚ) + 33 = (a : ℚ) + (c : ℚ) := by
    exact_mod_cast hb
  have hc' : (c : ℚ) = 44 := by
    linarith [h1, h2]
  have h_c : c = 44 := by
    exact_mod_cast hc'
  have h3 : (a : ℚ) = (b : ℚ) - 11 := by
    linarith [h1, hc']
  have h4 : a < 11 := by
    have h5 : (a : ℚ) < (11 : ℚ) := by
      linarith [hc, hc']
    exact_mod_cast h5
  have h5 : b ≥ 11 := by
    omega
  have h6 : b ≤ 21 := by
    omega
  omega