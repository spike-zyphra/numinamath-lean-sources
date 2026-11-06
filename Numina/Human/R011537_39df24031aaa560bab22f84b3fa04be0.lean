import Mathlib

theorem number_theory_6202 :
    IsLeast {x : ℕ | x > 37 ∧ x^2 % 11 = 4} 42 := by 
  constructor
  · -- We need to prove that $42 \in \{x \mid x > 37 \land x^2 \bmod 11 = 4\}$
    constructor
    · -- First, show that $42 > 37$
      norm_num 
    · -- Then, compute $42^2 \bmod 11$
      norm_num 
  · -- Now, we need to prove that $42$ is the smallest such element
    intro x h
    rcases h with ⟨hx1, hx2⟩
    by_contra h'
    push_neg at h'
    interval_cases x <;> norm_num at *