import Mathlib

theorem number_theory_88557 (p : ℕ) (hp : p.Prime) :
    ∃ x y : ℤ, x > 0 ∧ y > 0 ∧ x * (y ^ 2 - p) + y * (x ^ 2 - p) = 5 * p ↔
    p = 2 ∨ p = 3 ∨ p = 7 := by
  by_cases h : p ≤ 7
  · -- p ≤ 7 
    have h2 : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by 
      interval_cases p <;> norm_num at *
      <;> tauto 
    rcases h2 with (rfl | rfl | rfl | rfl)
    · -- p = 2 
      use 1, 4 
      all_goals norm_num
      <;> omega 
    · -- p = 3 
      use 2, 3 
      all_goals norm_num
      <;> omega 
    · -- p = 5 
      use 0, 0 
      norm_num 
      all_goals linarith 
    · -- p = 7 
      use 3, 4 
      all_goals norm_num
      <;> omega 
  · -- p > 7, i.e., p ≥ 11 since p is a prime.
    have h2 : p ≥ 11 := by
      by_contra h' -- Assume ¬(p ≥ 11)
      push_neg at h' -- h' becomes p < 11
      have h3 : p ≤ 10 := by omega -- From p < 11 for integer p
      have h4 : p < 11 := by omega -- Same as h3
      interval_cases p <;> norm_num at hp h h3 <;> all_goals try { contradiction } <;> all_goals try { tauto } 
      all_goals try { omega } 
    use 1, -1
    simp at *
    all_goals norm_num
    all_goals omega 
    all_goals tauto
    all_goals try { nlinarith <;> tauto }