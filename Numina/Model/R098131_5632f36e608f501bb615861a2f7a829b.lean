import Mathlib

theorem number_theory_121192 {n : ℕ} (hn : n ≠ 0) (h : 100 / n = 110 + 1) :
    n = 19 := by 
  have h2 : n ≤ 100 := by 
    by_contra h2
    push_neg at h2
    have h3 : 100 / n = 0 := by 
      rw [Nat.div_eq_zero_iff]
      omega
    omega 
  interval_cases n <;> norm_num at h <;> all_goals omega