import Mathlib

theorem number_theory_291120 {n : ℕ} (hn : n < 50) (h : 100 % n = 6) : n = 47 := by 
  have h1 : n > 0 := by
    by_contra h2
    push_neg at h2 
    have h3 : n = 0 := by linarith 
    rw [h3] at h 
    all_goals omega 
  interval_cases n <;> norm_num at h <;> all_goals omega