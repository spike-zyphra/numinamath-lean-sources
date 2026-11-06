import Mathlib

theorem number_theory_307533 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p + q = 85) : p * q = 166 := by
  have h1 : p ≤ 85 := by linarith
  have h2 : q ≤ 85 := by linarith
  interval_cases p <;> interval_cases q 
    <;> norm_num at h hp hq ⊢ 
    <;> tauto