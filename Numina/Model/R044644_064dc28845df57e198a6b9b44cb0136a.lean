import Mathlib

theorem algebra_299207 {a b : ℕ → ℤ} (ha : ∀ n, a n = n ^ 2 + n) (hb : ∀ n, b n = a n ^ 2 + 2 * a n + 3)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    a m ^ 2 + b n ^ 2 + m ^ 2 + n ^ 2 - 2 * (a m * b n + m * n) ≥ 5 := by
  have ha_m : (a m : ℤ) = (m ^ 2 + (m : ℤ)) := by
    rw [ha m]
    <;> ring_nf
  have ha_n : (a n : ℤ) = (n ^ 2 + (n : ℤ)) := by
    rw [ha n]
    <;> ring_nf
  have h2 : (b n : ℤ) = ( (n ^ 2 + (n : ℤ)) ^ 2 + 2 * (n ^ 2 + (n : ℤ)) + 3 ) := by
    rw [hb n, ha_n]
    <;> ring_nf
  have h1 : a m ^ 2 + b n ^ 2 + m ^ 2 + n ^ 2 - 2 * (a m * b n + m * n) = (a m - (b n : ℤ)) ^ 2 + (m - n) ^ 2 := by
    rw [h2, ha_m]
    nlinarith

  rw [h1]

  by_contra h
  push_neg at h
  
  have h5 : (a m - (b n : ℤ)) ^ 2 < 5 := by
    nlinarith

  have h6 : (m - n : ℤ) ^ 2 < 5 := by
    nlinarith
  
  have h7 : (a m - (b n : ℤ)) ^ 2 ≤ 4 := by
    omega

  have h8 : (m - n : ℤ) ^ 2 ≤ 4 := by
    omega
  
  have h9 : (a m - (b n : ℤ)) ≤ 2 := by 
    nlinarith
  
  have h10 : (a m - (b n : ℤ)) ≥ -2 := by 
    nlinarith
  
  have h11 : (m : ℤ) - (n : ℤ) ≤ 2 := by 
    nlinarith
  
  have h14 : (n : ℤ) - (m : ℤ) ≤ 2 := by 
    nlinarith
  
  have ha_m1 : (a m : ℤ) = (m ^ 2 + (m : ℤ)) := ha_m
  have ha_n1 : (a n : ℤ) = (n ^ 2 + (n : ℤ)) := ha_n
  have h22 : (b n : ℤ) = ( (n ^ 2 + (n : ℤ))^ 2 + 2 * (n ^ 2 + (n : ℤ)) + 3 ) := h2
  
  have hm1 : (m : ℤ) > 0 := by exact_mod_cast (show m > 0 by linarith [hm])
  have hn1 : (n : ℤ) > 0 := by exact_mod_cast (show n > 0 by linarith [hn])
  
  -- Now we how both functions bounded, need finite search
  -- Parameters to functions gcd, so that find bound.
  -- S impressive, that Lean could check ( require us to check all N cases
  -- Need o compute deterministic step
  
  have h70 : m ≤ n + 2 := by
    omega
  
  have h71 : n ≤ m + 2 := by
    omega
  
  -- Now finite to check with bounds
  
  have h100 : m ≤ 5 := by
    nlinarith [sq_nonneg ((m: ℤ) ^ 2 + (m: ℤ) - ((n ^ 2 + (n : ℤ)) ^ 2 + 2 * (n ^ 2 + (n : ℤ)) + 3)), sq_nonneg ((m: ℤ) - (n: ℤ)), h5, h6, sq_nonneg ((n: ℤ) ^ 2 + (n: ℤ) ^ 2), sq_nonneg ((m: ℤ)), sq_nonneg ((n: ℤ))]
  
  have h101 : n ≤ 5 := by
    nlinarith [sq_nonneg ((m: ℤ) ^ 2 + (m: ℤ) - ((n ^ 2 + (n: ℤ)) ^ 2 + 2 * (n ^ 2 + (n: ℤ)) + 3)), sq_nonneg ((m: ℤ) - (n: ℤ)), h5, h6, sq_nonneg ((m: ℤ) ^ 2 + (m: ℤ) ^ 2), sq_nonneg ((n: ℤ) ^ 2 + (n: ℤ) ^ 2)]

  interval_cases m <;> try { interval_cases n <;> norm_num [ha_m1, h22] at * <;> omega }
  <;> try { interval_cases n <;> norm_num [ha_m1, h22] at * <;> omega }
  <;> tauto
  <;> try { nlinarith }
  <;> tauto
  <;> norm_num <;> try { tauto } <;> nlinarith
  <;> try { tauto } <;> nlinarith <;> try { tauto }
  <;> norm_num