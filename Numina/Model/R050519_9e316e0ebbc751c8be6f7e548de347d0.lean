import Mathlib

theorem number_theory_195311 (A : ℕ) (hA : A < 100) (hA1 : A > 9)
    (h : (Nat.digits 10 A).sum ^ 2 = (Nat.digits 10 (A ^ 2)).sum) :
    A = 10 ∨ A = 11 ∨ A = 12 ∨ A = 13 ∨ A = 20 ∨ A = 21 ∨ A = 22 ∨
    A = 30 ∨ A = 31 := by
  interval_cases A <;> norm_num at h ⊢ <;> try simp <;> try trivial <;> norm_num
  <;> omega