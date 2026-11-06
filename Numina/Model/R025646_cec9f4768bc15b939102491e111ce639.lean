import Mathlib

theorem algebra_12707 :
    IsLeast {n | ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p > 20 ∧ q > 20 ∧ p ≠ q ∧ p * q = n} 667 := by
  constructor 
  · -- Show 667 is in the set
    use 23, 29
    all_goals norm_num 
  · -- Show there is no smaller element in the set
    intro n hn 
    rcases hn with ⟨p, q, hp, hq, hp2, hq2, hpneq, heq⟩ 
    by_contra h
    push_neg at h 
    have h32 : p ≤ 31 := by
      by_contra h4
      push_neg at h4 
      have h4' : q ≥ 21 := by omega 
      have h5 : p ≥ 32 := by omega 
      have h6 : p * q ≥ 672 := by
        nlinarith
      nlinarith
    have h33 : q ≤ 31 := by 
      by_contra h4 
      push_neg at h4 
      have h4' : p ≥ 21 := by omega 
      have h5 : q ≥ 32 := by omega 
      have h6 : p * q ≥ 672 := by 
        nlinarith
      nlinarith 
    interval_cases p <;> interval_cases q 
    <;> norm_num at hp hq hp2 hq2 hpneq heq 
    <;> omega