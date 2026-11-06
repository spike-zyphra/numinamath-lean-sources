import Mathlib


theorem algebra_324781 (x : ℝ) (hx : 2 * abs (Real.sin x) ^ (1 + 182) = 1 + abs (Real.sin x)) :
    ∃ k : ℤ, x = Real.pi / 2 + k * Real.pi := by
  have h1 : 0 ≤ abs (Real.sin x) := by
    apply abs_nonneg
  have h2 : abs (Real.sin x) ≤ 1 := by
    have h3 : -1 ≤ Real.sin x ∧ Real.sin x ≤ 1 := Real.sin_mem_Icc x
    have h4 : abs (Real.sin x) ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith
    linarith
  have h3 : 2 * abs (Real.sin x) ^ 183 = 1 + abs (Real.sin x) := by
    have h4 : abs (Real.sin x) ^ (1 + 182) = abs (Real.sin x) ^ 183 := by
      ring_nf
    rw [h4] at hx
    linarith
  have h4 : abs (Real.sin x) = 1 := by
    by_cases h7 : abs (Real.sin x) < 1
    ·
      have h5 : abs (Real.sin x) < 1 := h7
      have h7 : 2 * abs (Real.sin x) ^ 183 < 1 + abs (Real.sin x) := by
        have h14 : abs (Real.sin x) > 0 := by
          by_contra h0
          push_neg at h0
          have : abs (Real.sin x) = 0 := by
            linarith [abs_nonneg (Real.sin x), h0]
          rw [this] at h3
          nlinarith
        have h13 : abs (Real.sin x) ^ 183 < abs (Real.sin x) := by
          have h77 : abs (Real.sin x) < 1 := h7
          have h14 : abs (Real.sin x) > 0 := by
            by_contra h0
            push_neg at h0
            have : abs (Real.sin x) = 0 := by
              linarith [abs_nonneg (Real.sin x), h0]
            rw [this] at h3
            nlinarith
          have h13 : abs (Real.sin x) ^ 183 < abs (Real.sin x) := by
            have h92 : abs (Real.sin x) ^ 183 < abs (Real.sin x) := by
              have h103 : abs (Real.sin x) < 1 := h7
              have h104 : abs (Real.sin x) > 0 := h14
              have h105 : abs (Real.sin x) ^ 183 < abs (Real.sin x) := by
                have h131 : abs (Real.sin x) ^ 183 < abs (Real.sin x) := by
                  have h77 : abs (Real.sin x) < 1 := h7
                  have h132 : abs (Real.sin x) ^ 182 < 1 := by
                    have h104 : abs (Real.sin x) < 1 := h7
                    have h105 : abs (Real.sin x) ≥ 0 := abs_nonneg (Real.sin x)
                    have h106 : abs (Real.sin x) ^ 182 < (1 : ℝ) := by
                      apply pow_lt_one
                      all_goals
                        nlinarith
                    linarith
                  have h133 : abs (Real.sin x) > 0 := h14
                  have h134 : abs (Real.sin x) * (abs (Real.sin x) ^ 182) < abs (Real.sin x) := by
                    nlinarith [sq_nonneg (abs (Real.sin x) ^ 91), sq_nonneg (abs (Real.sin x) - 1)]
                  have h135 : abs (Real.sin x) ^ 183 = abs (Real.sin x) * (abs (Real.sin x) ^ 182) := by
                    ring
                  nlinarith
                linarith
              linarith
            linarith
          linarith
        nlinarith [sq_nonneg (abs (Real.sin x) ^ 91 - 1), sq_nonneg (abs (Real.sin x) - 1), sq_nonneg (abs (Real.sin x) ^ 2 - 1), sq_nonneg (abs (Real.sin x) ^ 3 - 1)]
      linarith
    ·
      have h77 : abs (Real.sin x) ≥ 1 := by linarith
      have h88 : abs (Real.sin x) = 1 := by
        linarith [abs_le.mp (show abs (Real.sin x) ≤ 1 by
          have h3 : -1 ≤ Real.sin x ∧ Real.sin x ≤ 1 := Real.sin_mem_Icc x
          have h4 : abs (Real.sin x) ≤ 1 := by
            apply abs_le.mpr
            constructor <;> linarith
          linarith
        ), h77]
      linarith
  have h7 : abs (Real.sin x) = 1  := h4
  have h8 : Real.sin x = 1 ∨ Real.sin x = -1  := by
    cases eq_or_eq_neg_of_abs_eq h7 with
    | inl h9 =>
      left
      linarith
    | inr h10 =>
      right
      linarith
  cases h8 with
  | inl h9 =>
    have h10 : ∃ k : ℤ, x = Real.pi / 2 + k * Real.pi := by
      have h11 : Real.sin x = 1 := h9
      obtain ⟨k, hk⟩ := Real.sin_eq_one_iff.1 h11
      use 2 * k
      field_simp at hk ⊢
      nlinarith [Real.pi_pos]
    exact h10
  | inr h10 =>
    have h10 : ∃ k : ℤ, x = Real.pi / 2 + k * Real.pi := by
      have h11 : Real.sin x = -1  := h10
      obtain ⟨k, hk⟩ := Real.sin_eq_neg_one_iff.1 h11
      use (2 * k - 1)
      field_simp at hk ⊢
      nlinarith [Real.pi_pos]
    exact h10