import Mathlib

theorem number_theory_287591 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p + q = 31) : p * q = 58 := by
  have h1 : p ≤ 31 := by linarith
  have h2 : q ≤ 31 := by linarith
  interval_cases p <;> interval_cases q
    <;> norm_num at hp hq h ⊢ 
    <;> all_goals trivial