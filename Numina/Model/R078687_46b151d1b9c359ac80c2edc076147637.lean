import Mathlib

theorem algebra_270105 {n : ℕ} (hn : n > 0) (h : (n * 100 + 2 * 25) % 100 = 0) :
    n = 8 := by 
        omega