import Mathlib

theorem algebra_178197 (n m b : ℕ)
    (hm : 28 ≤ m ∧ m ≤ 31)
    (hn : n * (m - 1) = 1100 - 820)
    (hb : n * (b - 1) = 1000 - 820) :
    b = 19 := by 
  have h1 : n * (m - 1) = 280 := by 
    omega
  have h2 : n * (b - 1) = 180 := by
    omega
  have h3 : m ≥ 28 := by omega 
  have h4 : m ≤ 31 := by omega 
  have h5 : m ≥ 28 := by omega
  have h6 : m ≤ 31 := by omega 
  interval_cases m <;> try { 
    omega 
  } <;> try { 
    norm_num at h1 h2 ⊢ 
    try { 
      have hn1 : n = 10 := by 
        omega 
      rw [hn1] at h2 
      have h3 : (b - 1) = 18 := by 
        omega 
      omega 
    } 
  }