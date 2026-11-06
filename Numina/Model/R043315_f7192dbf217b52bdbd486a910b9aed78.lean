import Mathlib

theorem number_theory_7241 (n : ℕ) (hn : n > 0) :
    ∃ x y z : ℤ, x^2 + y^2 = z^n := by 
  by_cases h : n % 2 = 1
  · -- n is odd
    have h1 : ∃ k, n = 2 * k + 1 := by 
      refine' ⟨(n - 1) / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    use (2 : ℤ) ^ k
    use (2 : ℤ) ^ k
    use (2 : ℤ)
    rw [hk]
    ring_nf
    <;> norm_num
    <;> ring
  · -- n is even
    have h2 : ∃ k, n = 2 * k := by 
      refine' ⟨n / 2, by omega⟩
    rcases h2 with ⟨k, hk⟩
    by_cases h3 : k > 0
    · -- k > 0, so k - 1 >= 0
      use (3 * (5 : ℤ) ^ (k - 1))
      use (4 * (5 : ℤ) ^ (k - 1))
      use (5 : ℤ)
      rw [hk]
      have h4 : (k : ℕ) > 0 := h3
      have h7 : ((3 * (5 : ℤ) ^ (k - 1)) : ℤ)^2 + ((4 * (5 : ℤ) ^ (k - 1)) : ℤ)^2 = (25 : ℤ) ^ k := by
        have h8 : (k - 1 : ℕ) = k - 1 := by omega
        have h9 : ((3 * (5 : ℤ) ^ (k - 1)) : ℤ)^2 + ((4 * (5 : ℤ) ^ (k - 1)) : ℤ)^2 = 
          (9 * ((5 : ℤ) ^ (k - 1) )^2 ) + (16 * ((5 : ℤ) ^ (k - 1) )^2 ) := by ring
        rw [h9]
        have h10 : (9 * ((5 : ℤ) ^ (k - 1) )^2 ) + (16 * ((5 : ℤ) ^ (k - 1) )^2 ) = (25 * ((5 : ℤ) ^ (k - 1) )^2 ) := by ring
        rw [h10]
        have h11 : (25 * ((5 : ℤ) ^ (k - 1) )^2 ) = (25 : ℤ) ^ k := by
          have h12 : ((5 : ℤ) ^ (k - 1) : ℤ) ^ 2 = (5 : ℤ) ^ (2 * (k - 1 : ℕ)) := by 
            ring_nf
          rw [h12]
          have h13 : 25 * ((5 : ℤ) ^ (2 * (k - 1 : ℕ)) ) = (25 : ℤ) ^ k := by
            have h14 : (25 : ℤ) ^ k = (5 ^ 2) ^ k := by
              norm_num
            rw [h14]
            have h15 : (5 : ℤ) ^ (2 * k) = (5 ^ 2) ^ k := by 
              rw [pow_mul]
              all_goals ring_nf
            have h16 : (5 : ℤ) ^ (2 * k) = (25 : ℤ) ^ k := by
              calc
                (5 : ℤ) ^ (2 * k) = ((5 : ℤ) ^ 2) ^ k := by rw [pow_mul]
                _ = (25 : ℤ) ^ k := by norm_num
            have h17 : 25 * ((5 : ℤ) ^ (2 * (k - 1 : ℕ)) ) = (5 : ℤ) ^ (2 * k : ℕ) := by
              have h18 : 25 * ((5 : ℤ) ^ (2 * (k - 1 : ℕ)) ) = (5 : ℤ) ^ 2 * ((5 : ℤ) ^ (2 * (k - 1 : ℕ)) ) := by
                norm_num
              rw [h18]
              have h19 : (5 : ℤ) ^ 2 * ((5 : ℤ) ^ (2 * (k - 1 : ℕ)) ) = (5 : ℤ) ^ (2 + 2 * (k - 1 : ℕ)) := by
                ring_nf
              rw [h19]
              have h20 : 2 + 2 * (k - 1 : ℕ) = (2 * k : ℕ) := by 
                omega
              rw [h20]
            rw [h17]
            all_goals try {rw [h16]; all_goals linarith}
          exact h13
        exact h11
      have h8 : ( (5 : ℤ) ^ (2 * k) ) = (25 : ℤ) ^ k := by 
        calc
          (5 : ℤ) ^ (2 * k) = ((5 : ℤ) ^ 2) ^ k := by rw [pow_mul]
          _ = (25 : ℤ) ^ k := by norm_num
      rw [h7, h8]
      all_goals try { ring_nf <;> norm_num }
    · -- k ≤ 0, so k = 0 because k is ℕ
      have h7 : k = 0 := by omega
      rw [h7] at hk
      have h8 : n = 0 := by 
        omega
      omega