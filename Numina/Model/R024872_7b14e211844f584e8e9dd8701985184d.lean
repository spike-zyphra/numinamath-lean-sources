import Mathlib

theorem number_theory_238790 {n : ℕ} (h : n * (Nat.digits 10 n).sum = 2008) :
    n = 251 := by
  have h1 : n ≤ 2008 := by
    by_contra h4
    push_neg at h4
    have h3 : n > 2008 := by linarith
    have h5 : n ≥ 1 := by
      by_contra h6
      push_neg at h6
      have h7 : n = 0 := by linarith
      rw [h7] at h
      omega
    have h8 : (Nat.digits 10 n).sum ≥ 1 := by
      by_contra h11
      push_neg at h11
      have h12 : (Nat.digits 10 n).sum = 0 := by
        omega
      rw [h12] at h
      omega
    nlinarith
  interval_cases n <;> norm_num at h ⊢ <;> all_goals try { trivial }
  <;> try { omega } <;> try { tauto }
  all_goals try { 
    omega
  }