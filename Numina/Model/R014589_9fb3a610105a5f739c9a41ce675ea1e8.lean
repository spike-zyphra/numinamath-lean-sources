import Mathlib

theorem algebra_221978 {n : ℕ} (hn : n > 0) (h : ∑ i ∈ Finset.range n, (15 + 2 * i) = m ^ 2) :
    n = 18 := by

  have h1 : ∀ n : ℕ, ∑ i in Finset.range n, (15 + 2 * i) = n * (n + 14) := by 
    intro n
    induction n with 
    | zero => 
      simp
    | succ n ih => 
      rw [Finset.sum_range_succ, ih]
      ring

  have h2 : n * (n + 14) = m ^ 2 := by 
    rw [h1 n] at h
    all_goals 
      norm_num at h ⊢
      all_goals omega

  have h3 : n ≤ m := by 
    by_contra h 
    push_neg at h 
    have h4 : m < n := by omega 
    have h5 : m ^ 2 < n * n := by 
      nlinarith [h4]
    have h6 : n * (n + 14) ≥ n * n := by 
      nlinarith [show 0 < (14 : ℕ) by norm_num]
    nlinarith [h2, h5, h6]

  have h4 : m ≤ n + 7 := by
    by_contra h 
    push_neg at h 
    have h5 : m > n + 7 := by omega 
    have h6 : m ^ 2 > (n + 7) ^ 2 := by
      nlinarith [h5]
    have h7 : n * (n + 14) < (n + 7) ^ 2 := by
      nlinarith [show 0 < (14 : ℕ) by norm_num]
    nlinarith [h2, h6, h7]

  have h11 : n ≤ 63 := by 
    by_contra h 
    push_neg at h 
    have h14 : m = n + 7 := by 
      nlinarith [h, h4, h3, h2, sq_nonneg (n : ℕ), sq_nonneg (m : ℕ)]
    rw [h14] at h2 
    ring_nf at h2 
    all_goals nlinarith

  interval_cases n <;> try { 
    { 
      have h12 : m ≤ 70 := by nlinarith 
      interval_cases m <;> omega 
    } 
  }