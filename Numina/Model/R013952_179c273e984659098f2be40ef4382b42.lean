import Mathlib

theorem algebra_233160 {n : ℕ} :
    IsGreatest {n | ∃ k, (n ^ 2 + 2002 * n) = k ^ 2} 500000 := by
  constructor
  · -- Show that 500000 is in the set
    use 501000
    all_goals
      norm_num
  · -- Show that for all n in the set, n ≤ 500000
    intro n hn
    rcases hn with ⟨k, hk⟩
    by_contra h
    push_neg at h
    have h1 : k < n + 1001 := by
      nlinarith [sq_nonneg (k : ℕ), sq_nonneg (n : ℕ), sq_nonneg ((n + 1001) : ℕ), 
        sq_nonneg (k - (n + 1001) : ℤ)
      ]
    have h2 : k ≥ n + 1001 := by
      by_contra h'
      push_neg at h'
      have h4 : k ≤ n + 1000 := by 
        omega
      have eq2 : (n + 1001 - k) * (n + 1001 + k) = 1001 ^ 2 := by
        have eq3 : (n : ℕ) ^ 2 + 2002 * n = k ^ 2 := by
          linarith
        ring_nf at eq3 ⊢
        nlinarith
      have h4' : (n + 1001 - k) * (n + 1001 + k) = 1001 ^ 2 := eq2
      -- We need to convert n and k to integers to handle possible negative values in the expression
      -- (k - (n + 1001)) can be negative, so we can't work with ℕ anymore
      -- We need to adjust h and h4 to account for the integer conversion
      -- Also need to adjust the original assumption h (n > 500000) to work with integers
      exfalso
      nlinarith [sq_nonneg (k - (n + 1001) : ℤ), sq_nonneg ((n : ℤ) - 500000 : ℤ), sq_nonneg ((k : ℤ) - 501000 : ℤ)]
    omega