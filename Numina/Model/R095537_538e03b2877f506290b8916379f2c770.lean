import Mathlib

theorem number_theory_183132 :
    IsLeast {a | ∃ b : ℕ, a.Prime ∧ a = b^2 - 10} 71 := by
  constructor
  · -- Show 71 is in the set
    use 9
    all_goals norm_num
  · -- Show no element less than 71 is in the set
    intro a ha
    rcases ha with ⟨b, hb_prime, hb_eq⟩
    by_contra h
    push_neg at h
    have h2 : b^2 < 81 := by 
      omega
    have h1 : b ≤ 8 := by 
      nlinarith
    interval_cases b <;> norm_num at hb_eq <;> 
      norm_num [hb_eq] at hb_prime <;> 
      all_goals linarith