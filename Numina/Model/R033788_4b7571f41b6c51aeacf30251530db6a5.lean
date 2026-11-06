import Mathlib

theorem number_theory_300852 (a : ℕ) (ha : a < 10) (h : ∃ n, n^2 = 1000 * (a + 1) + 100 * a + 10 * (a + 2) + (a + 3)) :
    a = 3 := by 
  rcases h with ⟨n, hn⟩
  have h1 : n^2 = 1111 * a + 1023 := by 
    ring_nf at hn ⊢ 
    omega
  have h6 : a ≤ 9 := by 
    omega
  have h7 : n ≤ 105 := by
    by_contra h
    push_neg at h
    have h3 : n ^ 2 ≥ 11111 := by
      nlinarith [show n ≥ 106 from by omega]
    nlinarith [show a ≤ 9 by omega, h1]
  interval_cases a <;> try { 
    interval_cases n <;> omega 
  }