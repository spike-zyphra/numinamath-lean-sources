import Mathlib

theorem number_theory_139966 (n : ℕ) (h : n > 0) (a : ℕ → ℕ)
    (ha : ∀ i, a i = a (i - 1) + i) (h0 : a 0 = 0) (h1 : a n = 6328) :
    n = 112 := by 
  have h2 : ∀ k, a k = k * (k + 1) / 2 := by 
    intro k 
    induction k with 
    | zero =>
      simp [h0]
      <;> try { omega }
    | succ k ih =>
      have h2 := ha (k + 1)
      simp [h2, ih] at *
      <;> ring_nf <;> omega 
  have h3 : a n = n * (n + 1) / 2 := h2 n
  rw [h3] at h1
  have h4 : n ≤ 112 := by 
    by_contra h5
    push_neg at h5
    have h5 : n ≥ 113 := by omega
    have h6 : n * (n + 1) / 2 > 6328 := by 
      have h7 : n ≥ 113 := by linarith 
      have h8 : n * (n + 1) ≥ 113 * 114 := by
        have h9 : n ≥ 113 := by linarith 
        have h10 : n + 1 ≥ 114 := by linarith 
        nlinarith [h9, h10] 
      have h9 : n * (n + 1) / 2 ≥ 113 * 114 / 2 := by 
        have h10 : n * (n + 1) ≥ 113 * 114 := by 
          have h9 : n ≥ 113 := by linarith 
          have h10 : n + 1 ≥ 114 := by linarith 
          nlinarith [h9, h10] 
        have h11 : n * (n + 1) / 2 ≥ 113 * 114 / 2 := by 
          apply Nat.div_le_div 
          all_goals nlinarith 
        linarith [h11] 
      have h10 : 113 * 114 / 2 > 6328 := by 
        norm_num 
      linarith [h9, h10] 
    linarith [h1, h6] 
  have h5 : n ≥ 112 := by 
    by_contra h6 
    push_neg at h6 
    have h6 : n ≤ 111 := by omega 
    have h7 : n * (n + 1) / 2 < 6328 := by 
      have h8 : n ≤ 111 := by linarith 
      have h9 : n * (n + 1) ≤ 111 * 112 := by 
        have h10 : n ≤ 111 := by linarith 
        have h11 : n + 1 ≤ 112 := by linarith 
        nlinarith [h10, h11] 
      have h10 : n * (n + 1) / 2 ≤ 111 * 112 / 2 := by 
        have h11 : n * (n + 1) ≤ 111 * 112 := by 
          have h10 : n ≤ 111 := by linarith 
          have h11 : n + 1 ≤ 112 := by linarith 
          nlinarith [h10, h11] 
        have h12 : n * (n + 1) / 2 ≤ 111 * 112 / 2 := by 
          apply Nat.div_le_div 
          all_goals nlinarith 
        linarith [h12] 
      have h11 : 111 * 112 / 2 < 6328 := by 
        norm_num 
      linarith [h10, h11] 
    linarith [h1, h7] 
  linarith [h4, h5]