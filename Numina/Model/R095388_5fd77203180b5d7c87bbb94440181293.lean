import Mathlib

theorem number_theory_203097 :
    IsLeast {k | ∃ m n, m > 0 ∧ n > 0 ∧ 3 * n^3 = 5 * m^2 ∧ k = m + n} 60 := by 
  constructor
  · -- First, show that there exist m and n such that (45, 15) satisfy the conditions (m + n = 60)
    use 45, 15
    all_goals norm_num 
  · -- Now, we need to show that no smaller element is in the set
    rintro k ⟨m, n, hm, hn, heq, hk⟩
    by_contra h
    push_neg at h
    have h1 : m ≤ 60 := by omega
    have h2 : n ≤ 60 := by omega
    interval_cases m <;> interval_cases n <;> omega