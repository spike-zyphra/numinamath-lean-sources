import Mathlib

theorem number_theory_319049 (a b c : ℕ) (ha : 0 < a) (hb : a < b) (hc : b < c)
    (h : a * b + b * c + c * a = a * b * c) :
    (a, b, c) = (2, 3, 6) := by
  have h1 : a ≤ 3 := by
    nlinarith [sq_pos_of_pos (show 0 < b - a by omega), sq_pos_of_pos (show 0 < c - b by omega), 
      sq_pos_of_pos (show 0 < c - a by omega), mul_pos ha (show 0 < b by nlinarith), 
      mul_pos (show 0 < b by nlinarith) (show 0 < c by nlinarith)]
  have h3 : a > 0 := by linarith
  interval_cases a <;> try { 
    all_goals
    norm_num at h ⊢
    all_goals
      have h4 : b ≤ 6 := by
        nlinarith [sq_pos_of_pos (show 0 < b by omega), sq_pos_of_pos (show 0 < c - b by omega), 
          sq_pos_of_pos (show 0 < c by omega), mul_pos (show 0 < b by omega) (show 0 < c by omega)]
      interval_cases b <;> omega
  }
  all_goals omega