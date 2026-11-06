import Mathlib

theorem algebra_20698 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hdiff : p ^ 2 - q ^ 2 = 1488) (h50 : p < 50 ∧ q < 50) : p = 43 ∧ q = 19 := by
  rcases h50 with ⟨hp50, hq50⟩
  have h1 : p ≤ 49 := by linarith
  have h2 : q ≤ 49 := by linarith
  interval_cases p <;> try { 
    interval_cases q <;> norm_num at hp hq hdiff hne ⊢ 
    <;> tauto 
  }