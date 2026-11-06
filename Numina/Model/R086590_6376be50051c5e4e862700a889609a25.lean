import Mathlib

theorem inequalities_237280 (n : ℕ) (hn : n > 0) (a b c d : ℚ)
    (ha : a = 1 / 2) (hb : b = 1 / 3) (hc : c = 1 / 10)
    (hd : d = 1 / n) (hsum : a + b + c + d < 1) :
    n > 15 := by

  rw [ha, hb, hc, hd] at hsum

  by_contra h
  push_neg at h
  have h1 : n ≤ 15 := by linarith
  interval_cases n <;> norm_num at hsum <;> all_goals 
    try { omega }