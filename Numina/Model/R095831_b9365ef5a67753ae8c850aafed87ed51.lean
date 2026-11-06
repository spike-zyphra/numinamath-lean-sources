import Mathlib

theorem algebra_232375 (n : ℕ) (h : n = 328 - (Nat.digits 10 n).sum) :
    n = 317 := by 
  have h1 : n ≤ 328 := by 
    omega
  interval_cases n <;> norm_num at h ⊢ <;> try { trivial }
  <;> try { linarith }
  <;> try { exfalso <;> omega }