import Mathlib

theorem algebra_12523 {n : ℕ} (hn : n > 0) (h : n^2 < 73 ∧ 73 < (n + 1)^2) :
    n * (n + 1) = 72 := by
  have h1 : n^2 < 73 := h.1
  have h2 : 73 < (n + 1)^2 := h.2

  have h3 : n ≤ 8 := by
    nlinarith
  
  have h4 : n ≥ 8 := by
    by_contra h'
    push_neg at h'
    have h5 : n ≤ 7 := by omega
    have h6 : (n + 1) ^ 2 ≤ 64 := by
      have h7 : n + 1 ≤ 8 := by omega
      have h8 : (n + 1) ^ 2 ≤ 8 ^ 2 := by
        apply Nat.pow_le_pow_of_le_left
        linarith
        all_goals omega
      norm_num at h8 ⊢
      linarith

    linarith

  have hn8 : n = 8 := by 
    omega
  
  calc
    n * (n + 1) = 8 * (8 + 1) := by rw [hn8]
    _ = 8 * 9 := by rfl
    _ = 72 := by norm_num