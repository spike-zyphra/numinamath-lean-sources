import Mathlib

theorem number_theory_159095 :
    IsLeast {k | ∃ n : ℕ, n > 0 ∧ k = 11 ^ n ∧ (k % 1000 = 1)} (11 ^ 50) := by
  constructor
  · -- We verify that 11^50 is in the set
    use 50
    all_goals norm_num
  · -- We verify that if k ∈ ℕ, k ∈ set ⇒ k ≥ 11^50
    intro k hk
    rcases hk with ⟨n, hn_pos, rfl, hn_mod⟩
    by_contra h
    push_neg at h
    have h1 : n < 50 := by
      by_contra h2
      push_neg at h2
      have h3 : n ≥ 50 := by linarith
      have h4 : (11 : ℕ) ^ n ≥ (11 : ℕ) ^ 50 := by
        have h5 : n ≥ 50 := h3
        have h6 : (11 : ℕ) ^ n ≥ (11 : ℕ) ^ 50 := by
          apply pow_le_pow_right
          all_goals linarith
        linarith
      linarith
    have h2 : n < 50 := h1
    have h3 : n < 50 := h1
    interval_cases n <;> norm_num at hn_mod ⊢ <;> all_goals try { omega }
    all_goals contradiction