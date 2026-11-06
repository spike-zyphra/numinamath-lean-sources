import Mathlib

theorem number_theory_2837 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
(h : 3 * p + 7 * q = 41) : (p + 1) * (q - 1) = 12 := by
  have h1 : p ≤ 13 := by linarith [h]
  have h2 : q ≤ 5 := by linarith [h]
  have h3 : q ≥ 2 := by
    by_contra h3
    push_neg at h3
    have h4 : q < 2 := by linarith
    interval_cases q <;> norm_num at hq <;> try { contradiction }
    all_goals omega

  have h4 : q = 2 ∨ q = 3 ∨ q = 5 := by
    interval_cases q <;> norm_num at hq <;> try { tauto }
  
  rcases h4 with hq2 | hq3 | hq5
  · -- Case q = 2
    have hq2' : q = 2 := by omega
    have hp9 : 3 * p = 27 := by
      rw [hq2'] at h
      omega
    have hp9' : p = 9 := by
      linarith [hp9]
    rw [hp9'] at hp
    norm_num at hp
    all_goals try contradiction
  · -- Case q = 3
    have hq3' : q = 3 := by omega
    have h1' : 3 * p = 20 := by 
      rw [hq3'] at h
      omega
    omega
  · -- Case q = 5
    have hq5' : q = 5 := by omega
    have eq1 : 3 * p = 6 := by
      rw [hq5'] at h
      omega
    have hp2 : p = 2 := by 
      omega
    calc 
      (p + 1) * (q - 1) = (2 + 1) * (5 - 1) := by rw [hp2, hq5']
      _ = 12 := by norm_num