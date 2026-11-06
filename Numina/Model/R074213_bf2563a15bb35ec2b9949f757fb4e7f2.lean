import Mathlib

theorem number_theory_147313 (a : ℕ → ℕ) (ha : ∀ n, a n = a (n - 1) + a (n - 2))
    (ha0 : a 0 = 1) (ha1 : a 1 = 2) :
    a 1998 = 2 ^ 1998 * 2001 := by 
  have h1 := ha 0
  simp at h1 
  all_goals 
    omega