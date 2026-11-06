import Mathlib

theorem algebra_196653 {a : ℕ} : a^(a^a) = (a^a)^a ↔ a = 1 ∨ a = 2 := by
  constructor
  · -- Forward: If \(a^{a^{a}} = (a^{a})^{a}\), then \(a = 1\) or \(a = 2\).
    intro h_eq
    have h_eq2 : a ≤ 2 := by
      by_contra h
      push_neg at h
      have h1 : a > 2 := by linarith
      have h2 : a ^ a ^ a > (a ^ a) ^ a := by
        have h3 : a > 2 := h1
        have h4 : a ^ a > a ^ 2 := by
          have h5 : a > 2 := h3
          have : a ^ a > a ^ 2 := by
            have : a ^ a > a ^ 2 := by
              apply Nat.pow_lt_pow_right
              all_goals nlinarith
            linarith
          linarith
        have : a ^ a ^ a > (a ^ a) ^ a := by
          have h5 : a ^ (a ^ a) > a ^ (a * a) := by
            have h6 : a ^ a > a ^ 2 := by linarith
            have h7 : a ^ a ≥ a ^ 2 + 1 := by
              omega
            have h8 : a ^ (a ^ a) > a ^ (a * a) := by
              have h9 : a ^ a > a * a := by
                nlinarith [show a >= 3 by linarith, show a ^ a >= a^3 by
                  have : a ^ a >= a ^ 3 := by
                    apply Nat.pow_le_pow_of_le_right (by linarith) (show a >= 3 by linarith)
                  linarith
                ]
              have h9' : a ^ (a ^ a) > a ^ (a * a) := by
                apply Nat.pow_lt_pow_right
                all_goals nlinarith
              linarith
            linarith
          have h6 : (a ^ a) ^ a = a ^ (a * a) := by
            rw [Nat.pow_mul]
          have h7 : a ^ a ^ a = a ^ (a ^ a) := by
            rfl
          have h8 : a ^ a ^ a > a ^ (a * a) := by
            linarith [h5, h7]
          have h9 : a ^ a ^ a > (a ^ a) ^ a := by
            nlinarith [h6, h8]
          linarith
        linarith
      linarith [h_eq, h2]
    interval_cases a <;> norm_num at h_eq <;> tauto
  · -- Backward: If \(a = 1\) or \(a = 2\), then \(a^{a^{a}} = (a^{a})^{a}\).
    rintro (h | h)
    · -- Case where \(a = 1\).
      rw [h]
      all_goals norm_num
    · -- Case where \(a = 2\).
      rw [h]
      all_goals norm_num
      <;> linarith