import Mathlib

def isLucky (a : ℕ) := (Nat.digits 10 a).sum = 7

theorem number_theory_276237 {a : ℕ → ℕ} (ha : ∀ n, isLucky (a n)) (ha1 : a 0 = 0)
    (ha2 : ∀ n, a (n + 1) > a n) (h : a 4 = 2005) :
    a (5 * 4) = 52000 := by 
  have h0 : isLucky (a 0) := ha 0
  rw [ha1] at h0
  simp [isLucky] at h0 
  all_goals linarith