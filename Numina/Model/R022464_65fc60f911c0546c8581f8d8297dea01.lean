import Mathlib

theorem number_theory_243462 (p v : ℕ) (hp : p > 0) (hv : v > 0)
    (h : p = (Nat.digits 10 v).sum) (h' : p + v = 2018) :
    p = 10 := by 
  have h1 : v ≤ 2017 := by
    omega
  rw [show p = (Nat.digits 10 v).sum by exact h] at h'
  interval_cases v <;> norm_num at h' h <;> try { all_goals omega }
  <;> try { all_goals tauto }
  <;> try { all_goals native_decide }