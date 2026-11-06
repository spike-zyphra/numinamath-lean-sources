import Mathlib

theorem number_theory_61393 (a : ℕ → ℕ)
  (h₀ : ∃ d, ∀ n, a n = a 0 + d * n)
  (h₁ : 0 < a 0)
  (h₂ : 0 < d)
  (h₃ : a 3 = 13) :
  
  a (a 1) + a (a 2) + a (a 3) + a (a 4) + a (a 5) ≤ 365 := by
  rcases h₀ with ⟨d, h₆⟩
  have eq3 : a 3 = a 0 + 3 * d := by
    rw [h₆ 3]
    ring_nf
  rw [eq3] at h₃
  have h4 : a 0 + 3 * d = 13 := by 
    omega
  have eq1 : a 1 = a 0 + d := by
    rw [h₆ 1]
    ring_nf
  have eq2 : a 2 = a 0 + 2 * d := by
    rw [h₆ 2]
    ring_nf
  have eq3' : a 3 = a 0 + 3 * d := by
    rw [h₆ 3]
    ring_nf
  have eq4 : a 4 = a 0 + 4 * d := by
    rw [h₆ 4]
    ring_nf
  have eq5 : a 5 = a 0 + 5 * d := by
    rw [h₆ 5]
    ring_nf
  have eq_a1 : a (a 1) = a 0 + d * (a 0 + d) := by
    rw [eq1]
    rw [h₆]
    all_goals  ring_nf
    all_goals omega
  have eq_a2 : a (a 2) = a 0 + d * (a 0 + 2 * d) := by
    rw [eq2]
    rw [h₆]
    all_goals  ring_nf
    all_goals omega
  have eq_a3 : a (a 3) = a 0 + d * (a 0 + 3 * d) := by
    rw [eq3']
    rw [h₆]
    all_goals  ring_nf
    all_goals omega
  have eq_a4 : a (a 4) = a 0 + d * (a 0 + 4 * d) := by
    rw [eq4]
    rw [h₆]
    all_goals  ring_nf
    all_goals omega
  have eq_a5 : a (a 5) = a 0 + d * (a 0 + 5 * d) := by
    rw [eq5]
    rw [h₆]
    all_goals  ring_nf
    all_goals omega
  rw [eq_a1, eq_a2, eq_a3, eq_a4, eq_a5]
  have h5 : d ≤ 4 := by 
    omega
  interval_cases d <;> try { 
    omega 
  }
  <;> norm_num at h4 h₁
  <;> try { 
    all_goals
    have : a 0 ≤ 13 := by
      omega
    interval_cases a 0 <;> omega 
  }
  <;> try { 
    all_goals 
    omega 
  }
  <;> norm_num 
  <;> try { 
    all_goals 
    try { 
      tauto 
    }
  }
  <;> try { 
    all_goals
    interval_cases a 0 <;> omega 
  }
  <;> try { 
    all_goals
    nlinarith
  }