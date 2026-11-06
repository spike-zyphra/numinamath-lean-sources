import Mathlib

theorem number_theory_251792 (y : ℕ) (hy : y ≤ 1984) (h : 1984 - y = (Nat.digits 10 y).sum) :
    1984 - y = 20 := by
  interval_cases y <;> norm_num at h ⊢ <;> try { tauto } <;> omega