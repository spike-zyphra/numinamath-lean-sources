import Mathlib

theorem number_theory_279896 (n : ℕ) (h : n > 0) (a b c : ℕ)
    (ha : a = n * (n + 1) / 2) (hb : b = n * (n + 2) / 2)
    (hc : c = n * (n + 3) / 2) (h1 : a = b + 55) :
    n = 41 := by 
  rw [ha, hb] at h1
  have h2 : n ≤ 112 := by
    by_contra h
    push_neg at h 
    have h3 : n * (n + 1) / 2 ≤ n * (n + 2) / 2 := by 
      have h4 : n * (n + 1) ≤ n * (n + 2) := by 
        nlinarith 
      have h5 : n * (n + 1) / 2 ≤ n * (n + 2) / 2 := by 
        apply Nat.div_le_div_right 
        all_goals 
          omega 
      linarith 
    omega 
  interval_cases n <;> omega