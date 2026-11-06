import Mathlib

theorem number_theory_100829 :
    ¬∃ a b c : ℕ, a ≠ 0 ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧
      IsSquare ((a * 100 + b * 10 + c) + (b * 100 + c * 10 + a) + (c * 100 + a * 10 + b)) := by
  rintro ⟨a, b, c, ha, ha9, hb9, hc9, h⟩
  have h1 : a ≤ 9 := by linarith
  have h2 : b ≤ 9 := by linarith
  have h3 : c ≤ 9 := by linarith
  have h4 : (a * 100 + b * 10 + c) + (b * 100 + c * 10 + a) + (c * 100 + a * 10 + b) = 111 * (a + b + c) := by
    omega
  rw [h4] at h
  have h5 : a + b + c ≤ 27 := by 
    omega
  have h6 : a + b + c ≥ 1 := by 
    omega
  rcases h with ⟨k, hk⟩
  have h7 : k ≤ 75 := by
    nlinarith [show a + b + c ≤ 27 by omega, sq_nonneg (k : ℕ)]
  interval_cases k <;> try { 
    omega 
  }
  all_goals
  try { 
    interval_cases h8 : a + b + c <;> omega 
  }
  all_goals 
  try { 
    contradiction 
  }