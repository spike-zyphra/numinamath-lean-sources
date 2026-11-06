import Mathlib

/- If $m, n$ are positive integers, and $n^{3} = 756m$, then the minimum value of $mn$ is ___          ___. -/
theorem number_theory_7950 :
    IsLeast {k | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ n^3 = 756 * m ∧ k = m * n} 4116 := by
  constructor
  · -- Show that 4116 is in the set
    use 98, 42
    all_goals norm_num
  · -- Show that 4116 is the least element in the set
    intro k hk
    rcases hk with ⟨m, n, hm, hn, h_eq, hk⟩
    by_contra h
    push_neg at h
    have h1 : m * n < 4116 := by 
      linarith
    have h2 : n ≤ 125 := by
      by_contra h3
      push_neg at h3
      have h3' : n ≥ 126 := by linarith
      have h4 : n ^ 4 ≥ 126 ^ 4 := by
        have h5 : n ≥ 126 := h3'
        have h6 : n ^ 4 ≥ 126 ^ 4 := by
          have h7 : n ≥ 126 := h5
          have h8 : n ^ 4 ≥ 126 ^ 4 := by
            apply Nat.pow_le_pow_of_le_left
            omega
          linarith
        linarith
      nlinarith [sq_nonneg (n: ℕ), sq_nonneg ((m: ℕ) : ℕ), sq_nonneg ((m * n: ℕ) : ℕ),
        sq_nonneg ((n ^ 3: ℕ) : ℕ), sq_nonneg ((756 * m: ℕ) : ℕ),
        h_eq, h1, hm, hn]
    interval_cases n <;> omega