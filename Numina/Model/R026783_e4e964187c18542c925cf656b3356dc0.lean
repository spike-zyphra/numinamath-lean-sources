import Mathlib

theorem number_theory_72396 (a k m : ℕ) (ha : 0 < a) (hk : 0 < k) (hm : 0 < m)
    (h : k + a ^ k = m + 2 * a ^ m) :
    ∃ t, (a, k, m) = (1, t + 1, t) := by
  by_cases h3a : a > 1
  · -- Assume a > 1
    have h1 : k > m := by
      by_contra h8
      push_neg at h8 
      have h90 : k ≤ m := by omega
      have h91 : a ^ k ≤ a ^ m := by
        apply Nat.pow_le_pow_of_le_right 
        all_goals linarith 
      have h14 := h 
      have h14_eq : k + a ^ k = m + 2 * a ^ m := by linarith 
      have h15 : k ≤ m := by omega 
      have h90 : k + a ^ k ≤ m + a ^ m := by 
        have h17 : a ^ k ≤ a ^ m := h91
        omega 
      have h141 : m + 2 * a ^ m = k + a ^ k := by linarith 
      have h142 : m + 2 * a ^ m ≤ m + a ^ m := by 
        linarith [show k + a ^ k ≤ m + a ^ m from h90]
      have h143 : 2 * a ^ m ≤ a ^ m := by 
        linarith 
      have h144 : a ^ m > 0 := by 
        apply Nat.pow_pos 
        linarith 
      have h145 : a ^ m ≤ 0 := by 
        nlinarith 
      linarith
    -- Now we have k > m
    have h2a : k ≥ m + 1 := by omega 
    have h5 : a ^ k ≥ 2 * a ^ m := by 
      have h6 : k ≥ m + 1 := h2a 
      have h7 : a ^ k ≥ a ^ (m + 1) := by 
        apply Nat.pow_le_pow_of_le_right 
        all_goals linarith 
      have h811 : a ^ (m + 1) ≥ 2 * a ^ m := by 
        have ha2 : a ≥ 2 := by omega 
        have h79 : a ^ (m + 1) = a * (a ^ m) := by ring 
        rw [h79] 
        have h80 : a ≥ 2 := ha2 
        have h81 : a * (a ^ m) ≥ 2 * (a ^ m) := by 
          have h82 : a ≥ 2 := by linarith 
          have h83 : (a ^ m) > 0 := by 
            apply Nat.pow_pos 
            linarith 
          nlinarith 
        linarith 
      linarith 
    linarith
  · -- Assume a ≤ 1
    have h4a : a = 1 := by 
      linarith 
    use m 
    simp [h4a] at h ⊢ 
    all_goals 
      omega