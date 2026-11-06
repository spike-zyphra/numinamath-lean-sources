import Mathlib

theorem algebra_98206
 {n : ℕ} (hn : Odd n)
 (h : n + 2 = 3 * n) : n + (n + 2) = 4 := by

 rw [h]

 have h1 : n = 1 := by linarith

 rw [h1]