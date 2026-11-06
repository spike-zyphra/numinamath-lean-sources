import Mathlib

theorem number_theory_306358 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : 5 * p + 3 * q = 91) :
    p = 17 ∧ q = 2 := by
  have hp1 : p ≤ 30 := by
    by_cases h1 : p ≤ 30
    · linarith
    · -- contradiction
      push_neg at h1
      have h2 : 5 * p > 91 := by
        omega
      have h3 : 3 * q ≥ 0 := by 
        omega
      omega

  have hq1 : q ≤ 30 := by
    by_cases h2 : q ≤ 30
    · linarith
    · -- contradiction
      push_neg at h2
      have h3 : 3 * q > 91 := by 
        omega
      have h4 : 5 * p ≥ 0 := by 
        omega
      omega
  
  interval_cases p <;> interval_cases q <;> norm_num at h hp hq ⊢ <;> tauto