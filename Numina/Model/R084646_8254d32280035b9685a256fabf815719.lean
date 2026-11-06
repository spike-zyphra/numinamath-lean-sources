import Mathlib

theorem algebra_253023 (x : ℕ) (h : 3^(x - 1) + 5^(x - 1) = 34) : x = 3 := by
  have h1 : x ≥ 1 := by
    by_contra hx
    push_neg at hx
    have h2 : x = 0 := by omega
    rw [h2] at h
    norm_num at h
    all_goals linarith

  have h2 : x ≤ 4 := by
    by_contra hx
    push_neg at hx
    have h4 : x ≥ 5 := by omega
    have h3 : 3 ^ (x - 1) ≥ 81 := by
      have h6 : x - 1 ≥ 4 := by omega
      have h7 : 3 ^ (x - 1) ≥ 3 ^ 4 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) h6
      norm_num at h7 ⊢
      linarith
    have h5 : 5 ^ (x - 1) ≥ 625 := by
      have h9 : x - 1 ≥ 4 := by omega
      have h10 : 5 ^ (x - 1) ≥ 5 ^ 4 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) h9
      norm_num at h10 ⊢
      linarith
    linarith
  have h3 : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
  rcases h3 with (r | r | r | r)
  · -- Case x = 1
    rw [r] at h
    norm_num at h
    all_goals linarith
  · -- Case x = 2
    rw [r] at h
    norm_num at h
    all_goals linarith
  · -- Case x = 3
    exact r
  · -- Case x = 4
    rw [r] at h
    norm_num at h
    all_goals linarith