import Mathlib

theorem number_theory_100187 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : ∃ k, k^2 = 52 * a + 364 * b) :
    a + b ≥ 7 := by 
  by_contra h'
  push_neg at h'
  rcases h with ⟨k, hk⟩
  have h1 : a + b < 7 := by 
    omega
  have h2 : a ≤ 5 := by
    omega
  have h3 : b ≤ 5 := by
    omega
  have h4 : k ≤ 45 := by
    nlinarith [show 52 * a + 364 * b ≤ 2080 by
      interval_cases a <;> interval_cases b
      <;> omega
    , hk]
  interval_cases k <;> norm_num at hk
  all_goals 
    omega