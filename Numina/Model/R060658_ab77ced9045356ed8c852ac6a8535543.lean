import Mathlib

theorem number_theory_17186 (p h : ℕ) (hp : p = 2713147) (hh : h < 10000) (h1 : (Nat.digits 10 h).length = 4)
    (h2 : (Nat.digits 10 h).toFinset.card = 4) (h3 : (Nat.digits 10 p).sum = (Nat.digits 10 h).sum) :
    h ≤ 9871 := by
  rw [hp] at h3
  norm_num at h3

  by_contra h'
  push_neg at h'

  interval_cases h <;> norm_num at h1 h2 h3 ⊢ <;> all_goals contradiction
  all_goals contradiction