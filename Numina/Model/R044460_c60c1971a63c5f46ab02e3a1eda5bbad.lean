import Mathlib

theorem number_theory_182397 (p q : ℤ) (hp : 1 < p) (hq : 1 < q)
    (h1 : q ∣ 2 * p - 1) (h2 : p ∣ 2 * q - 1) : p + q = 8 := by
  have h3 : q ≤ 2 * p - 1 := by
      apply Int.le_of_dvd (by omega) h1
  have h4 : p ≤ 2 * q - 1 := by
      apply Int.le_of_dvd (by omega) h2
  by_cases h : p ≤ 5
  · -- case p ≤ 5
    have h7 : q ≤ 9 := by 
      nlinarith [show q ≤ 2 * p - 1 from h3, h]
    interval_cases p <;> try { 
      omega 
    }
    <;> try { 
      have h8 : q ≤ 9 := h7
      interval_cases q <;> omega 
    }
  · -- case p > 5
    have hp1 : 5 < p := by
      omega
    exfalso
    obtain ⟨k, hk1⟩ := h1
    obtain ⟨l, hl1⟩ := h2
    have hk2 : k ≥ 1 := by
      have h11 : (2 * p - 1) > 0 := by 
        omega
      have h12 : q ≥ 2 := by 
        omega
      have h13 : k ≥ 1 := by
        nlinarith
      omega
    have hl2 : l ≥ 1 := by
      have h11 : (2 * q - 1) > 0 := by
        omega
      have h12 : p ≥ 2 := by
        omega
      have h13 : l ≥ 1 := by
        nlinarith
      omega
    have hk11 : k ≤ 3 := by
      nlinarith [sq_nonneg (k - 3 : ℤ), sq_nonneg (l - 3 : ℤ), mul_pos (show 0 < p by omega) (show 0 < q by omega)]
    have hl11 : l ≤ 3 := by
      nlinarith [sq_nonneg (k - 3 : ℤ), sq_nonneg (l - 3 : ℤ), mul_pos (show 0 < p by omega) (show 0 < q by omega)]
    interval_cases k <;> interval_cases l <;> omega