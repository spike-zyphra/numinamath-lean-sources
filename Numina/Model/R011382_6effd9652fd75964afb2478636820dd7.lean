import Mathlib

theorem algebra_240215 (c : Fin 7 → ℕ) (m : Fin 6 → ℕ) (hc : ∀ i, c (i + 1) = (m i + 4 * c i) % 10)
  (h : c 0 = 1 ∧ c 2 = 3 ∧ c 4 = 7 ∧ c 6 = 1) :
  m = ![1, 3, 0, 9, 2, 1] → c = ![1, 5, 3, 2, 7, 0, 1] := by
  intro hm
  rcases h with ⟨hc0, hc2, hc4, hc6⟩
  have eq1 : c 1 = 5 := by
    have hc1 : c 1 = (m 0 + 4 * c 0) % 10 := by 
      simpa using hc 0
    rw [show m 0 = 1 by 
      rw [hm]
      simp 
    ] at hc1 
    rw [hc0] at hc1
    omega 
  have eq3 : c 3 = 2 := by 
    have hc3 : c 3 = (m 2 + 4 * c 2) % 10 := by 
      simpa using hc 2 
    rw [show m 2 = 0 by 
      rw [hm]
      simp 
    ] at hc3 
    rw [show c 2 = 3 by exact_mod_cast hc2] at hc3 
    omega 
  have eq5 : c 5 = 0 := by 
    have hc5 : c 5 = (m 4 + 4 * c 4) % 10 := by 
      simpa using hc 4 
    rw [show m 4 = 2 by 
      rw [hm]
      simp 
    ] at hc5 
    rw [show c 4 = 7 by exact_mod_cast hc4] at hc5 
    omega 
  funext i 
  fin_cases i <;> simp [hm, hc0, hc2, hc4, hc6, eq1, eq3, eq5, hc] at *
  all_goals try { omega }
  all_goals try { tauto }