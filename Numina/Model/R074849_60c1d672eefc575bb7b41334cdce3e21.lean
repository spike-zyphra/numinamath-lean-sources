import Mathlib

theorem number_theory_299202 (a b c d : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9)
    (hc : 1 ≤ c ∧ c ≤ 9) (hd : 0 ≤ d ∧ d ≤ 9) (h : ∃ n, n^3 = 200000 + 10000 * a + 1000 * b + 100 * c + 10 * d + 8) :
    a * 10 + b + c * 10 + d = 70 := by 
  rcases h with ⟨n, hn⟩
  have h1 : n ≥ 58 := by 
    by_contra h1
    push_neg at h1
    have h2 : n ≤ 57 := by 
      omega
    have h3 : n^3 < 200000 := by 
      have h4 : n ≤ 57 := h2
      have h5 : n^3 ≤ (57 : ℕ)^3 := by 
        apply Nat.pow_le_pow_of_le_left
        linarith
      norm_num at h5
      linarith
    have h4 : n^3 ≥ 200000 := by 
      nlinarith [show a ≥ 1 by linarith [ha.left], show c ≥ 1 by linarith [hc.left]]
    linarith
  have h2 : n ≤ 67 := by 
    by_contra h2
    push_neg at h2
    have h3 : n ≥ 68 := by 
      omega
    have h4 : n^3 > 299999 := by 
      have h5 : n ≥ 68 := h3
      have h6 : n^3 ≥ (68 : ℕ)^3 := by 
        apply Nat.pow_le_pow_of_le_left
        linarith
      norm_num at h6
      linarith
    have h5 : n^3 ≤ 299998 := by 
      have h6 : n^3 = 200000 + 10000 * a + 1000 * b + 100 * c + 10 * d + 8 := hn
      have h7 : a ≤ 9 := by linarith [ha.right]
      have h8 : b ≤ 9 := by linarith [hb.right]
      have h9 : c ≤ 9 := by linarith [hc.right]
      have h10 : d ≤ 9 := by linarith [hd.right]
      omega
    linarith
  interval_cases n <;> omega
  all_goals 
    omega