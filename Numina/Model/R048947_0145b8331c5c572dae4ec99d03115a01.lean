import Mathlib

theorem number_theory_161107 (n : ℕ) (h : n > 0) :
    ¬∃ m, n * (n + 1) * (n + 2) = m ^ 3 := by
    rintro ⟨m, hm⟩
    have h1 : n < m := by
      have h2 : n ^ 3 < n * (n + 1) * (n + 2) := by
        have eq : n * (n + 1) * (n + 2) = n ^ 3 + 3 * n ^ 2 + 2 * n := by
          ring_nf
        rw [eq]
        nlinarith [show n > 0 by linarith]
      have h3 : n ^ 3 < m ^ 3 := by linarith [hm, h2]
      have h4 : n < m := by
        by_contra h5
        push_neg at h5
        have h6 : m ≤ n := by linarith [h5]
        have h7 : m ^ 3 ≤ n ^ 3 := by
          apply Nat.pow_le_pow_of_le_left h6 3
        linarith
      linarith
    have h5 : m < n + 1 := by
      have h6 : m ^ 3 < (n + 1) ^ 3 := by
        have h7 : n * (n + 1) * (n + 2) < (n + 1) ^ 3 := by
          nlinarith [show n > 0 by linarith]
        have h8 : m ^ 3 = n * (n + 1) * (n + 2) := by linarith [hm]
        linarith [h7, h8]
      have h7 : m < n + 1 := by
        by_contra h8
        push_neg at h8
        have h9 : n + 1 ≤ m := by linarith [h8]
        have h10 : (n + 1) ^ 3 ≤ m ^ 3 := by
          apply Nat.pow_le_pow_of_le_left h9 3
        linarith
      linarith
    have h6 : n < m := h1
    have h7 : m < n + 1 := h5
    omega