import Mathlib

theorem number_theory_239785 {n m : ℕ} (hn : n > 0) (hm : m > 0)
    (h : (n^2 - m^2) = 124) :
    n^2 = 1024 := by 
  have eq1 : n ^ 2 - m ^ 2 = 124 := h
  have eq3 : n ^ 2 = m ^ 2 + 124 := by
    have eq2 : n ^ 2 - m ^ 2 = 124 := h
    have eq5 : n ^ 2 = m ^ 2 + 124 := by
      omega
    linarith 
  have eq4 : n > m := by
    by_contra h5
    push_neg at h5
    have eq5 : n ≤ m := by 
      omega
    have eq6 : n ^ 2 ≤ m ^ 2 := by 
      nlinarith
    nlinarith
  have h14 : m ≤ n := by
    have h2 : n > m := eq4
    omega
  have eq8 : n ≤ 64 := by
    nlinarith [sq_nonneg (m : ℕ), sq_nonneg (n : ℕ)]
  have eq9 : m ≤ 64 := by
    nlinarith [sq_nonneg (m : ℕ), sq_nonneg (n : ℕ)]
  interval_cases m <;> try { 
    omega 
  } <;> try { 
    have eq11 : n ≤ 64 := by
      omega 
    interval_cases n <;> omega 
  }