import Mathlib

theorem number_theory_106256 (n : ℕ) :
    n / 8 + n % 9 = 13 ↔ n = 108 ∨ n = 100 ∨ n = 92 ∨ n = 84 ∨ n = 76 ∨ n = 68 ∨ n = 60 ∨ n = 52 ∨ n = 44 := by 
  constructor
  · -- Assume n / 8 + n % 9 = 13, prove the disjunction.
    intro h 
    have h1 : n ≤ 112 := by 
      omega 
    interval_cases n <;> norm_num at h ⊢ 
    <;> omega
  · -- Assume the disjunction, prove n / 8 + n % 9 = 13.
    intro h 
    rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals norm_num 
    <;> omega