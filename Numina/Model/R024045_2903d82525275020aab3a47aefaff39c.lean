import Mathlib

theorem number_theory_4291 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h : (6 * a + 1) * (5 * b + 1) * (b ^ 3 + 1) = 804) : a + b = 12 := by
  have h1 : b ≤ 9 := by
    by_contra h2
    push_neg at h2
    have h3 : b ≥ 10 := by omega
    have h4 : a ≥ 1 := by 
      omega
    have h5 : (6 * a + 1) * (5 * b + 1) * (b ^ 3 + 1) ≥ 7 * 51 * 1001 := by
      have h51 : (6 * a + 1) ≥ 7 := by nlinarith
      have h52 : (5 * b + 1) ≥ 51 := by nlinarith
      have h53 : (b ^ 3 + 1) ≥ 1001 := by
        have h6 : b ≥ 10 := h3
        have h7 : b ^ 3 ≥ 1000 := by
          have h8 : b ≥ 10 := h6
          nlinarith [sq_nonneg ((b : ℤ) - 10 : ℤ), sq_nonneg ((b : ℤ) + 1 : ℤ), sq_nonneg ((b : ℤ) - 10 : ℤ)]
        nlinarith
      have h54 : (6 * a + 1) * (5 * b + 1) ≥ 7 * 51 := by
        nlinarith
      have e1 : (6 * a + 1) * (5 * b + 1) * (b ^ 3 + 1) = ((6 * a + 1) * (5 * b + 1)) * (b ^ 3 + 1) := by ring
      rw [e1]
      nlinarith
    have e1 : (6 * a + 1) * (5 * b + 1) * (b ^ 3 + 1) = 804 := by linarith [h]
    nlinarith
  have h2 : b ≥ 1 := by 
    omega
  interval_cases b <;> try { 
    ring_nf at h 
    have h3 : a ≤ 140 := by 
      nlinarith 
    interval_cases a <;> omega 
  }