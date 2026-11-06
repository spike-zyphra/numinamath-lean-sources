import Mathlib

def f (m : ℕ) := (m % 10)

theorem number_theory_302317 (a : ℕ → ℕ) (ha : ∀ n, a n = f (2 ^ (n + 1) - 1)) :
    a 1994 = 7 := by 
  rw [ha 1994]
  native_decide