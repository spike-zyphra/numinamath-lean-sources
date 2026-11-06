import Mathlib

theorem number_theory_5098 (a : ℕ) (ha : 0 < a) :
    ¬ ∃ n, n^2 = a * (a + 1) * (a + 2) * (a + 3) := by
  rintro ⟨n, hn⟩
  have h1 : a * (a + 1) * (a + 2) * (a + 3) = (a ^ 2 + 3 * a) * (a ^ 2 + 3 * a + 2) := by ring
  rw [h1] at hn
  have h2 : (a ^ 2 + 3 * a) ^ 2 < n^2 := by
    nlinarith [hn, sq_pos_of_pos (show 0 < (a : ℕ) by linarith), sq_pos_of_pos (show 0 < (a + 1 : ℕ) by linarith), sq_pos_of_pos (show 0 < (a + 2 : ℕ) by linarith), sq_pos_of_pos (show 0 < (a + 3 : ℕ) by linarith)]
  -- Show that n is upper bounded
  have h4 : n^2 < (a ^ 2 + 3 * a + 1) ^ 2 := by
    nlinarith [hn, sq_pos_of_pos (show 0 < (a : ℕ) by linarith), sq_pos_of_pos (show 0 < (a + 1 : ℕ) by linarith), sq_pos_of_pos (show 0 < (a + 2 : ℕ) by linarith), sq_pos_of_pos (show 0 < (a + 3 : ℕ) by linarith)]
  have h5 : (a ^ 2 + 3 * a : ℕ) < n := by
    by_contra h
    push_neg at h
    have h7 : n ≤ a ^ 2 + 3 * a := by linarith
    have h8 : (a ^ 2 + 3 * a) ^ 2 ≥ n^2 := by
      have h9 : n ≤ a ^ 2 + 3 * a := h7
      have h10 : (a ^ 2 + 3 * a : ℕ) ≥ n := by linarith
      have h11 : ((a ^ 2 + 3 * a) : ℕ) ^ 2 ≥ ((n : ℕ) : ℕ) ^ 2 := by
        apply Nat.pow_le_pow_left
        linarith
      linarith
    nlinarith
  have h7 : n < a ^ 2 + 3 * a + 1 := by
    by_contra h
    push_neg at h
    have h8 : n ≥ a ^ 2 + 3 * a + 1 := by linarith
    have h9 : n^2 ≥ (a ^ 2 + 3 * a + 1) ^ 2 := by
      have h10 : n ≥ a ^ 2 + 3 * a + 1 := h8
      have h11 : (n : ℕ) ≥ (a ^ 2 + 3 * a + 1 : ℕ) := h10
      have h12 : ((n : ℕ) : ℕ) ^ 2 ≥ ((a ^ 2 + 3 * a + 1 : ℕ) : ℕ) ^ 2 := by
        apply Nat.pow_le_pow_left
        linarith
      linarith
    nlinarith
  omega