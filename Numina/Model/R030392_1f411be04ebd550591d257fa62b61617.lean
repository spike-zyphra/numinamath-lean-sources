import Mathlib

def isLucky (a : ℕ) := (Nat.digits 10 a).sum = 7

theorem number_theory_114810 {a : ℕ → ℕ} (ha : ∀ i, isLucky (a i)) (ha' : a 0 = 0)
    (ha'' : ∀ n, a (n + 1) > a n) (h : a 4 = 2005) :
    a 20 = 52000 := by
  have h1 : isLucky (a 0) := ha 0
  rw [ha'] at h1
  norm_num [isLucky] at h1
  all_goals linarith