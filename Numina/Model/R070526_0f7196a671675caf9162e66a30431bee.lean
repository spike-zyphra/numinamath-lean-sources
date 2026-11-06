import Mathlib

theorem algebra_192870 (n : ℕ) (h : n < 10) (h' : 2 * (2 * n + 16) + 16 = 68) :
    n = 5 ∨ n = 9 := by 
  have hn : n = 5 := by
    omega
  simp [hn]