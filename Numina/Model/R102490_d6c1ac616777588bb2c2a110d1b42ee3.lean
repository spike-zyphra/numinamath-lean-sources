import Mathlib

theorem number_theory_269803 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hsum : p ≠ q) (hsum1 : p + q = 10) :
    p * q = 21 := by
  have h1 : p ≤ 10 := by linarith
  have h2 : q ≤ 10 := by linarith
  interval_cases p <;> interval_cases q 
    <;> norm_num at hp hq hsum1 ⊢ <;> try { contradiction } 
    <;> try { tauto }