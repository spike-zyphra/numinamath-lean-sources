import Mathlib

theorem number_theory_203542 (n : ℕ) (h : n > 0) (p q r : ℕ)
    (hpqr : p.Prime ∧ q.Prime ∧ r.Prime) (hsum : ∑ i ∈ Finset.range 25, (n + i) = p * q * r) :
    p + q + r ≥ 23 := by
  have h6 : p + q + r ≥ 23 := by 
    by_contra h2 
    push_neg at h2 
    have h6 : p + q + r ≤ 22 := by 
      omega 
    have hp2 : p ≥ 2 := Nat.Prime.two_le hpqr.1 
    have hq2 : q ≥ 2 := Nat.Prime.two_le hpqr.2.1 
    have hr2 : r ≥ 2 := Nat.Prime.two_le hpqr.2.2 

    have eq1 : ∑ i ∈ Finset.range 25, (n + i) = 25 * n + 300 := by 
      simp [Finset.sum_range_succ]
      <;> ring 
    have h5 : p * q * r = 25 * n + 300 := by 
      have h4 : ∑ i ∈ Finset.range 25, (n + i) = p * q * r := by 
        linarith [hsum]
      linarith [eq1, h4]

    have h5' : n ≥ 1 := by 
      omega 
    have h9 : p ≤ 22 := by 
      omega 
    have h10 : q ≤ 22 := by 
      omega 
    have h11 : r ≤ 22 := by 
      omega 
    interval_cases p <;> 
      try { 
        omega 
      }
      <;> interval_cases q 
      <;> norm_num at hpqr h5
      <;> all_goals try { 
        interval_cases r 
        <;> norm_num at hpqr h5 
        <;> omega 
      }
  linarith