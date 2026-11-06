import Mathlib
theorem algebra_607358 (a b c : ℝ) :
    a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a ^ 2 + a * b = c ∧ b ^ 2 + b * c = a ∧ c ^ 2 + c * a = b ↔
    (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 1 / 2 ∧ b = 1 / 2 ∧ c = 1 / 2) := by
  constructor
  · -- Assume the left side, prove the right
    rintro ⟨ha, hb, hc, h1, h2, h3⟩
    have h4 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h5 : a - b = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h6 : b - c = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have ha1 : a = b := by linarith
    have hb1 : b = c := by linarith
    have h7 : a = c := by linarith
    have h8 : a = 0 ∨ a = 1 / 2 := by
      have h9 : a * (2 * a - 1) = 0 := by
        nlinarith [h1, h7, ha1, hb1, ha, hb, hc]
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- h10 : a = 0
        left
        linarith
      · -- h11 : 2 * a - 1 = 0
        right
        linarith
    cases h8 with
    | inl ha0 =>
      have hb0 : b = 0 := by
        linarith [ha1, ha0
        ]
      have hc0 : c = 0 := by
        linarith [hb1, hb0
        ]
      left
      exact ⟨ha0, hb0, hc0⟩
    | inr ha1_2 =>
      have hb1_2 : b = 1 / 2 := by
        linarith [ha1, ha1_2
        ]
      have hc1_2 : c = 1 / 2 := by
        linarith [hb1, hb1_2
        ]
      right
      exact ⟨ha1_2, hb1_2, hc1_2⟩
  · -- Assume the right side, prove the left
    rintro (h | h)
    · -- Case (0, 0, 0)
      rcases h with ⟨ha, hb, hc⟩
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · nlinarith
      constructor
      · nlinarith
      · nlinarith
    · -- Case (1/2, 1/2, 1/2)
      rcases h with ⟨ha, hb, hc⟩
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · nlinarith
      constructor
      · nlinarith
      · nlinarith