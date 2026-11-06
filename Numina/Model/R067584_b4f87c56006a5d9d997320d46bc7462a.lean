import Mathlib

open Real

theorem inequalities_267837 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 4 ≤ a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) +
    c / ((c + 1) * (a + 1)) ∧
    (3 / 4 = a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) +
    c / ((c + 1) * (a + 1)) ↔ a = b ∧ b = c) := by
  constructor
  · -- Prove the first part: 3 / 4 ≤ ...
    have h1 : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) - 3 / 4 ≥ 0 := by
      have h2 : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) - 3 / 4 =
          (4 * (a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1))) - 3) / 4 := by
        ring_nf
      rw [h2]
      have h3 : 4 * (a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1))) - 3 ≥ 0 := by 
        have h4 : 0 < (a + 1) * (b + 1) := by positivity
        have h5 : 0 < (b + 1) * (c + 1) := by positivity
        have h6 : 0 < (c + 1) * (a + 1) := by positivity
        have h8 : 4 * (a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1))) - 3 =
            (4 * a * (c + 1) + 4 * b * (a + 1) + 4 * c * (b + 1) - 3 * ( (a + 1) * (b + 1) * (c + 1) ) ) / 
            ( (a + 1) * (b + 1) * (c + 1) ) := by
          field_simp
          ring
        rw [h8]
        have h9 : (4 * a * (c + 1) + 4 * b * (a + 1) + 4 * c * (b + 1) - 3 * ( (a + 1) * (b + 1) * (c + 1) ) ) ≥ 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc ]
        have h10 : (a + 1) * (b + 1) * (c + 1) > 0 := by positivity
        apply div_nonneg
        linarith
        all_goals linarith
      linarith
    linarith
  · -- Prove the second part: equality holds iff a = b = c
    constructor
    · -- Assume equality holds, prove a = b = c
      intro heq
      have h1 : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) - 3 / 4 = 0 := by linarith
      have h2 : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) - 3 / 4 =
          (4 * (a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1))) - 3) / 4 := by 
        ring_nf
      rw [h2] at h1
      have h3 : 4 * (a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1))) - 3 = 0 := by
        linarith
      have h4 : 4 * (a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1))) - 3 =
          (4 * a * (c + 1) + 4 * b * (a + 1) + 4 * c * (b + 1) - 3 * ( (a + 1) * (b + 1) * (c + 1) ) ) / 
          ( (a + 1) * (b + 1) * (c + 1) ) := by
        field_simp
        ring
      rw [h4] at h3
      have h5 : 4 * a * (c + 1) + 4 * b * (a + 1) + 4 * c * (b + 1) - 3 * ( (a + 1) * (b + 1) * (c + 1) )  = 0 := by
        have h6 : (a + 1) * (b + 1) * (c + 1) ≠ 0 := by 
          positivity
        field_simp at h3 ⊢
        nlinarith
      have h6 : (a - b)^2 + (b - c)^2 + (c - a)^2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc ]
      have h7 : a - b = 0 := by nlinarith
      have h8 : b - c = 0 := by nlinarith
      have ha1 : a = b := by linarith
      have hb1 : b = c := by linarith
      exact ⟨ha1, hb1⟩
    · -- Assume a = b = c, prove equality holds
      rintro ⟨rfl, rfl⟩
      have ha1 : a = 1 := by
        have h1 : a^2 * a = 1 := by
          nlinarith
        have h2 : a^3 = 1 := by
          nlinarith
        have h3 : a^3 - 1 = 0 := by
          nlinarith
        have h4 : (a - 1) * (a^2 + a + 1) = 0 := by
          ring_nf at h3 ⊢
          linarith
        cases (mul_eq_zero.mp h4) with
        | inl h5 =>
          linarith
        | inr h6 =>
          have h7 : a^2 + a + 1 > 0 := by
            nlinarith [sq_nonneg (a + 0.5)]
          nlinarith
      rw [ha1]
      norm_num