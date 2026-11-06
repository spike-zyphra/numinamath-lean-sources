import Mathlib

theorem number_theory_199408 {a b c d n m : ℕ} (ha : a < 10) (hb : b < 10)
    (hc : c < 10) (hd : d < 10) (h1 : n^2 = 2000 + 100 * a + 10 * b + 9)
    (h2 : m^2 = 2000 + 100 * c + 10 * d + 9) (h3 : m > n) :
    (m + n, 10 * a + b + 10 * c + d) = (100, 100) := by

  have h4 : n ≤ 54 := by
    nlinarith [h1, ha, hb]
  
  have h5 : n ≥ 45 := by
    nlinarith [h1, ha, hb]

  have h6 : m ≤ 54 := by
    nlinarith [h2, hc, hd]

  have h7 : m ≥ 45 := by
    nlinarith [h2, hc, hd]

  have h8 : n ≤ 54 := h4
  have h9 : n ≥ 45 := h5
  have h10 : m ≤ 54 := h6
  have h11 : m ≥ 45 := h7
  
  interval_cases n <;> try { 
    omega
  }
  <;> try { 
    interval_cases m <;> norm_num at h1 h2 h3 
    <;> norm_num [Prod.ext_iff] at *
    <;> omega 
  }