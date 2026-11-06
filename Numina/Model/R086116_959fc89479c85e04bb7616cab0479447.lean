import Mathlib

theorem number_theory_667 (x : ℕ) (hx : x > 0) (h : x = (Nat.digits 10 1995).sum - (Nat.digits 10 x).sum) :
    x = 21 := by
  have h1 : x ≤ 24 := by
    norm_num [Nat.digits, Nat.digitsAux] at h ⊢
    omega
  interval_cases x <;> norm_num [Nat.digits, Nat.digitsAux] at h ⊢ <;> omega