import Mathlib

theorem number_theory_274992 :
    IsLeast {a | ∃ b : ℕ, a.Prime ∧ a = b^2 - 10} 71 := by 
  constructor
  · -- Show 71 is in the set
    use 9
    all_goals norm_num
  · -- Show there is no smaller element in the set
    intro a ha
    rcases ha with ⟨b, h_prime, heq⟩
    by_contra h
    push_neg at h
    have h1 : b ≤ 8 := by 
      by_contra h2
      push_neg at h2 
      have h2' : b ≥ 9 := by omega 
      have h3 : (b : ℕ) ^ 2 ≥ 81 := by nlinarith 
      have h4 : (b ^ 2 : ℕ) ≥ 81 := h3 
      omega 
    interval_cases b <;> norm_num [heq] at *
    all_goals 
      norm_num at h_prime
      all_goals tauto