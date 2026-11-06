import Mathlib

theorem number_theory_100932 (a b c d n A : ℕ)
  (ha : a ∈ Finset.Icc 1 9)
  (hb : b ∈ Finset.range 10)
  (hc : c ∈ Finset.range 10)
  (hd : d ∈ Finset.range 10)
  (hA : A = 1000 * a + 100 * b + 10 * c + d) -- A is a four-digit number
  (hn : n ∈ Finset.Icc 1 9 ∧ n ≤ b ∧ n ≤ d) -- n is a digit that alters A and can be subtracted from b and d
  (h : 1000 * (a + n) + 100 * (b - n) + 10 * (c + n) + (d - n) = n * A) : A = 1818 := by 
  have h1 : a ≥ 1 := by 
    simp [Finset.mem_Icc] at ha 
    omega
  have ha2 : a ≤ 9 := by 
    simp [Finset.mem_Icc] at ha 
    omega 
  -- b < 10, so b is digit 0-9.
  have hb1 : b < 10 := by 
    simp [Finset.mem_range] at hb 
    omega 
  -- c < 10, so c is digit 0-9.
  have hc1 : c < 10 := by 
    simp [Finset.mem_range] at hc 
    omega 
  -- d < 10, so d is digit 0-9.
  have hd1 : d < 10 := by 
    simp [Finset.mem_range] at hd 
    omega 
  -- n is in [1,9]
  have hn11 : n ≥ 1 := by 
    have hn2 : n ∈ Finset.Icc 1 9 := hn.1 
    simp [Finset.mem_Icc] at hn2 
    omega 
  have hn12 : n ≤ 9 := by 
    have hn2 : n ∈ Finset.Icc 1 9 := hn.1 
    simp [Finset.mem_Icc] at hn2 
    omega 
  have h2 : n ≤ b := hn.2.1 
  have h3 : n ≤ d := hn.2.2 
  rw [hA] at h 
  by_cases h_n1 : n ≤ 5 
  · -- Case 1: n ≤ 5 
    have hn5 : n ≤ 5 := h_n1 
    have h4 : n ≥ 1 := by linarith 
    interval_cases n <;> 
      try { 
        omega 
      } 
  · -- Case 2: n > 5
    have hn6 : n > 5 := by omega 
    have hn9 : n ≤ 9 := by linarith 
    have h5 : n ≥ 6 := by omega 
    have hn5 : n ≤ 9 := by omega 
    have h6 : n ≥ 6 := by omega 
    interval_cases n <;> 
      try { 
        omega 
      }