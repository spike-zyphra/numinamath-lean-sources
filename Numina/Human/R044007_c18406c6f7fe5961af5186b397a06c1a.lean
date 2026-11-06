import Mathlib

theorem number_theory_290234 :
    IsGreatest {n | 200 < n ∧ n < 250 ∧ ∃ k, k^2 = 12 * n} 243 := by
  constructor
  · -- First, we verify that $243$ belongs to the set
    refine ⟨by norm_num, by norm_num, ⟨54, by norm_num⟩⟩
  · -- Now, we need to show maximality
    intro n hn
    rcases hn with ⟨hn1, hn2, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 244 := by linarith
    have h2 : n ≤ 249 := by linarith
    interval_cases n <;> 
    { 
      have : k ≤ 54 := by nlinarith
      have : k ≥ 55 := by nlinarith
      linarith
    }