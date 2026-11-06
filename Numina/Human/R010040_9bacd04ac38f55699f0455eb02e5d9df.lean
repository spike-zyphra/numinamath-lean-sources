import Mathlib

/- Leah has (A) 33(B) 35(C) 37(D) 39(E) 41 -/
theorem algebra_94843 (p n : ℕ) (h₀ : p + n = 13) (h₁ : n + 1 = p) :
5 * n + p = 37 := by
-- first solve the system of equation given by h₀ and h₁ then substitute the values. 
  rw[← h₁] at h₀
  have h : n = 6 := by linarith
  have k : p = 7 := by linarith
  rw[h, k]