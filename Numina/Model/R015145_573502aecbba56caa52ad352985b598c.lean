import Mathlib

theorem algebra_246239 {a : ℕ → ℤ} (ha1 : a 1 = 2)
    (han : ∀ n ≥ 1, a (n + 1) = a n ^ 2 - a n + 1) :
    ∀ n ≥ 2, a n ≥ 2 ^ (n - 1) + 1 := by 
  intro n hn
  have h3 : ∀ n, n ≥ 2 → a n ≥ 2 ^ (n - 1) + 1 := by 
    intro n hn 
    have h4 : n ≥ 2 := by linarith 
    have base2 : a 2 ≥ 2 ^ (2 - 1) + 1 := by 
      have ha2 : a 2 = a 1 ^ 2 - a 1 + 1 := han 1 (by norm_num)
      rw [ha2, ha1]
      all_goals norm_num 
    have step : ∀ m, m ≥ 2 → a m ≥ 2 ^ (m - 1) + 1 → a (m + 1) ≥ 2 ^ ((m + 1) - 1) + 1 := by 
      intro m hm h 
      have h6 : a (m + 1) = a m ^ 2 - a m + 1 := by 
        specialize han m (by linarith) 
        simpa using han 
      rw [h6] 
      have h3' : a m ≥ 2 ^ (m - 1) + 1 := h 
      have h4' : a m ^ 2 - a m + 1 ≥ (2 : ℤ) ^ m + 1 := by 
        have h9 : a m ≥ (2 : ℤ) ^ (m - 1) + 1 := h3'
        have h7' : (a m: ℤ) ^ 2 - (a m: ℤ) + 1 ≥ ((2 : ℤ) ^ (m - 1) + 1: ℤ) ^ 2 - ((2 : ℤ) ^ (m - 1) + 1: ℤ) + 1 := by 
          have h11 : a m ≥ (2 : ℤ) ^ (m - 1) + 1 := h3'
          nlinarith [sq_nonneg (a m - ((2 : ℤ) ^ (m - 1) + 1 : ℤ)), sq_nonneg ( (2 : ℤ) ^ (m-1) +1 ), 
            show (2 : ℤ) ^ (m - 1) ≥ 0 by positivity
          ]
        have h7 : ((2 : ℤ) ^ (m - 1) + 1) ^ 2 - ((2 : ℤ) ^ (m - 1) + 1) + 1 ≥ (2 : ℤ) ^ m + 1 := by 
          have h8 : ((2 : ℤ) ^ (m - 1) + 1) ^ 2 - ((2 : ℤ) ^ (m - 1) + 1) + 1 = 
            ((2 : ℤ) ^ (m - 1)) ^ 2 + (2 : ℤ) ^ (m - 1) + 1 := by 
            ring 
          rw [h8]
          have h9 : ((2 : ℤ) ^ (m - 1)) ^ 2 + (2 : ℤ) ^ (m - 1) + 1 ≥ (2 : ℤ) ^ m + 1 := by 
            have h10 : (2 : ℤ) ^ (m - 1) ≥ 1 := by 
              have h21 : m - 1 ≥ 1 := by 
                omega 
              have h11 : (2 : ℤ) ^ (m - 1) ≥ (2 : ℤ) ^ 1 := by 
                apply pow_le_pow_right 
                all_goals linarith 
              have h12 : (2 : ℤ) ^ 1 = (2 : ℤ) := by norm_num 
              have h13 : (2 : ℤ) ^ (m - 1) ≥ (2 : ℤ) := by linarith [h11, h12] 
              linarith 
            have h14 : ((2 : ℤ) ^ (m - 1)) ^ 2 + (2 : ℤ) ^ (m - 1) ≥ 2 * (2 : ℤ) ^ (m - 1) := by 
              nlinarith [sq_nonneg ((2 : ℤ) ^ (m - 1) - (1 : ℤ)), sq_nonneg ((2 : ℤ) ^ (m - 1)), 
                show (2 : ℤ) ^ (m - 1) ≥ 0 by positivity
              ]
            have h15 : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by 
              cases m with 
              | zero => linarith -- impossible 
              | succ n => 
                cases n with 
                | zero => linarith -- impossible 
                | succ n => 
                  simp [pow_add, pow_mul, pow_succ] 
                  <;> ring 
            linarith [h14, h15] 
          linarith 
        linarith [h7']
      -- Now simplify 2^(m+1 - 1) + 1 to 2^m + 1
      have h5 : (2 : ℤ) ^ ((m + 1) - 1) + 1 = (2 : ℤ) ^ m + 1 := by 
        cases m with 
        | zero => 
          all_goals simp 
        | succ m => 
          simp [pow_succ] 
          <;> ring 
      linarith [h4', h5] 
    exact Nat.le_induction base2 step n hn 
  specialize h3 n hn 
  simpa using h3