import Mathlib

theorem number_theory_217777 (m n : ℕ) :
    ∃ k, k^2 = 6^m + 2^n + 2 ↔ (m = 1 ∧ n = 3) := by
  use 4
  constructor
  · -- Assume k = 4, prove k^2 = 6^m + 2^n + 2 → (m = 1 ∧ n = 3)
    intro h
    have h1 : 6^m + 2^n = 14 := by
      omega
    have h2 : m ≤ 1 := by
      by_contra h
      push_neg at h
      have h3 : 6^m ≥ 36 := by
        have h4 : m ≥ 2 := by linarith
        have h5 : 6^m ≥ 6^2 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h6 : 6^2 = 36 := by norm_num
        linarith [h6, h5]
      have h7 : 2^n ≥ 0 := by positivity
      omega
    have h3 : m = 0 ∨ m = 1 := by
      omega
    rcases h3 with (h3 | h3)
    · -- Assume m = 0
      have h4 : m = 0 := h3
      rw [h4] at h1
      have h5 : 2^n = 13 := by
        omega
      have h6 : n ≤ 10 := by
        by_contra h
        push_neg at h
        have h7 : 2^n ≥ 2^11 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h8 : 2^11 = 2048 := by norm_num
        omega
      interval_cases n <;> norm_num at h5
    · -- Assume m = 1
      have h4 : m = 1 := h3
      rw [h4] at h1
      have h5 : 2^n = 8 := by
        omega
      have h6 : n = 3 := by
        have h7 : 2^n = 8 := h5
        have h8 : n = 3 := by
          have h9 : 2^n = 2^3 := by
            rw [h7]
            all_goals norm_num
          have h10 : n = 3 := by
            exact Nat.pow_right_injective (by norm_num) h9
          linarith
        linarith
      exact ⟨by linarith, h6⟩
  · -- Assume m = 1 ∧ n = 3, prove k^2 = 6^m + 2^n + 2
    rintro ⟨hm, hn⟩
    rw [hm, hn]
    all_goals norm_num