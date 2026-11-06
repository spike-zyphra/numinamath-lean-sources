import Mathlib

theorem number_theory_105900 (a : ℕ → ℕ) (ha1 : a 1 = 1989 ^ 1989)
    (han : ∀ n > 1, a n = (Nat.digits 10 (a (n - 1))).sum) :
    a 5 = 9 := by
  have h1 : a 1 = 1989 ^ 1989 := ha1
  have h2 : a 2 = (Nat.digits 10 (a 1)).sum := by apply han 2 (by norm_num)
  have h3 : a 3 = (Nat.digits 10 (a 2)).sum := by apply han 3 (by norm_num)
  have h4 : a 4 = (Nat.digits 10 (a 3)).sum := by apply han 4 (by norm_num)
  have h5 : a 5 = (Nat.digits 10 (a 4)).sum := by apply han 5 (by norm_num)
  rw [h5, h4, h3, h2, h1]
  native_decide