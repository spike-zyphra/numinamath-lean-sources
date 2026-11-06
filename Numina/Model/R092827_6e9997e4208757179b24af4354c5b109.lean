import Mathlib

theorem number_theory_229242 (n : ℕ) (h₀ : Even n) (h₁ : n * (n + 2) * (n + 4) * (n + 6) = 13440) :
    n = 8 := by 
  have h2 : n ≤ 20 := by
    by_contra h
    push_neg at h 
    have h3 : n ≥ 20 := by omega
    have h4 : n * (n + 2) * (n + 4) * (n + 6) > 13440 := by
      have h5 : n ≥ 20 := by linarith 
      have h6 : n + 2 ≥ 22 := by omega 
      have h7 : n + 4 ≥ 24 := by omega 
      have h8 : n + 6 ≥ 26 := by omega 
      have h9 : n * (n + 2) * (n + 4) * (n + 6) ≥ 20 * 22 * 24 * 26 := by 
        have h10 : n ≥ 20 := by linarith 
        have h11 : n + 2 ≥ 22 := by omega 
        have h12 : n + 4 ≥ 24 := by omega 
        have h13 : n + 6 ≥ 26 := by omega 
        have h14 : n * (n + 2) ≥ 20 * 22 := by 
          nlinarith 
        have h15 : (n + 4) * (n + 6) ≥ 24 * 26 := by 
          nlinarith 
        have h16 : (n * (n + 2)) * ((n + 4) * (n + 6)) ≥ (20 * 22) * (24 * 26) := by 
          nlinarith [h14, h15] 
        have h17 : n * (n + 2) * (n + 4) * (n + 6) = (n * (n + 2)) * ((n + 4) * (n + 6)) := by 
          ring 
        linarith [h16, h17] 
      norm_num at h9 ⊢ 
      linarith 
    linarith 
  interval_cases n <;> try { 
    norm_num at h₁ <;> try { 
      tauto 
    }
  }
  <;> try { 
    exfalso 
    norm_num at h₁ 
  }