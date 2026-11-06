import Mathlib

theorem number_theory_177247 {p q r : ℕ} (hpqr : p.Prime ∧ q.Prime ∧ r.Prime)
    (hqr : r - q = 2 * p) (hpr : r * q + p ^ 2 = 676) :
    p * q * r = 2001 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  -- Show r >= q
  have h1 : r ≥ q := by
    by_contra h
    push_neg at h
    have h2 : 2 * p = 0 := by
      omega
    have hp0 : p = 0 := by
      linarith
    rw [hp0] at hp
    norm_num at hp
    all_goals trivial
  have h_eq1 : r = q + 2 * p := by
    omega
  rw [h_eq1] at hpr
  -- Solve the equations
  have h_eq2 : (p + q) ^ 2 = 676 := by 
    nlinarith
  have h_eq3 : p + q = 26 := by
    nlinarith [h_eq2, hp, hq]
  have h_eq4 : p ≤ 26 := by
    omega
  have h_eq5 : q = 26 - p := by
    omega
  have h_eq6 : r = 26 + p := by
    omega
  interval_cases p <;> norm_num [h_eq5, h_eq6] at *
  <;> try { contradiction }
  <;> norm_num [h_eq5, h_eq6]
  <;> try { contradiction }
  <;> try { tauto }