import Mathlib

theorem number_theory_323941 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : 3 * p^2 + 5 * q = 517) : p + q = 103 ∨ p + q = 15 := by
  have h1 : p ≤ 13 := by
    by_contra h2
    push_neg at h2
    have h2' : p ≥ 14 := by linarith
    nlinarith [show 3 * p^2 ≥ 3 * 14^2 from by nlinarith [show p ≥ 14 by linarith, show p ^ 2 ≥ 14 ^ 2 by apply Nat.pow_le_pow_of_le_left h2' 2]]
  interval_cases p <;> try { 
    norm_num at h 
    <;> try { 
      have hq2 : q ≤ 103 := by nlinarith
      interval_cases q <;> norm_num at h <;> norm_num at hp hq <;> tauto
    }
    <;> contradiction
  }