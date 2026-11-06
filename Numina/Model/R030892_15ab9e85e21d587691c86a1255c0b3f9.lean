import Mathlib

theorem algebra_380691 (a : ℕ → ℤ) (ha1 : a 1 = 4) (han : ∀ n, a (n + 1) - a n = 3) :
    ∀ n > 0, n ≤ 6 → a n = 3 * n + 1 := by 
  intro n npos hn
  have ha1' : a 0 = 1 := by
    have eq1 := han 0
    simp at eq1 
    linarith [ha1]
  have ha2 : a 2 = 7 := by 
    have eq1 := han 1 
    simp [ha1] at eq1 
    linarith 
  have ha3 : a 3 = 10 := by 
    have eq1 := han 2 
    simp [ha2] at eq1 
    linarith
  have ha4 : a 4 = 13 := by 
    have eq1 := han 3 
    simp [ha3] at eq1 
    linarith 
  have ha5 : a 5 = 16 := by
    have eq1 := han 4 
    simp [ha4] at eq1 
    linarith 
  have ha6 : a 6 = 19 := by
    have eq1 := han 5 
    simp [ha5] at eq1 
    linarith
  have h1 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by 
    omega 
  rcases h1 with (rfl | rfl | rfl | rfl | rfl | rfl)
  · -- n = 1
    simp [ha1]
  · -- n = 2 
    simp [ha2]
  · -- n = 3 
    simp [ha3]
  · -- n = 4 
    simp [ha4]
  · -- n = 5 
    simp [ha5]
  · -- n = 6 
    simp [ha6]