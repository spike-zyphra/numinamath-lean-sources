import Mathlib

theorem algebra_181812 {a b : ℕ} (ha : a = (5 / 7 : ℚ) * b) (hb : b ≠ 0)
    (h : a + 3 = (4 / 5 : ℚ) * (b - 3)) :
    a = 45 := by 
  have h1 : (a : ℚ) = (5 / 7) * (b : ℚ) := by 
    exact_mod_cast ha
  have h2 : ((a : ℚ) + 3) = (4 / 5) * ((b : ℚ) - 3) := by
    exact_mod_cast h
  rw [h1] at h2
  have h3 : (b : ℚ) = 63 := by
    linarith
  have h4 : (a : ℚ) = 45 := by
    rw [h3] at h1
    linarith
  exact_mod_cast h4