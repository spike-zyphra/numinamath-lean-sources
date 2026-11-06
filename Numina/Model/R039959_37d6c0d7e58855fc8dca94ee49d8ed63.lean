import Mathlib

open Real

theorem inequalities_209608 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 / 2) * (a + b)^2 + (1 / 4) * (a + b) ≥ a * sqrt b + b * sqrt a ∧
    ((1 / 2) * (a + b)^2 + (1 / 4) * (a + b) = a * sqrt b + b * sqrt a ↔ a = b ∧ (a = 0 ∨ b = 1/4) ∧ (b = 0 ∨ a = 1/4)) := by 
  constructor
  · -- First part: prove the inequality
    nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a - 1 / 2), sq_nonneg (sqrt b - 1 / 2),
      mul_nonneg ha hb, 
      Real.sq_sqrt (show 0 ≤ a by linarith),
      Real.sq_sqrt (show 0 ≤ b by linarith), 
      sq_nonneg (a + b - 1 / 2), 
      Real.sqrt_nonneg a, 
      Real.sqrt_nonneg b, 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  · -- Second part: prove when equality holds
    constructor
    · -- Forward: equality implies a = b ∧ (a = 0 ∨ b = 1/4) ∧ (b = 0 ∨ a = 1/4)
      intro heq 
      have h1 : (sqrt a - sqrt b) ^ 2 = 0 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith), 
          sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a - 1 / 2), sq_nonneg (sqrt b - 1 / 2), 
            sq_nonneg (a + b - 1 / 2), Real.sqrt_nonneg a, Real.sqrt_nonneg b, 
              mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
                heq, mul_nonneg ha (show 0 ≤ b by linarith)]
      have h2 : sqrt a = sqrt b := by 
        nlinarith 
      have h3 : a = b := by 
        have h4 : sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
        have h5 : sqrt b ^ 2 = b := Real.sq_sqrt (by linarith) 
        rw [h2] at h4 
        nlinarith 
      have h6 : 2 * a ^ 2 + a / 2 = 2 * a * sqrt a := by
        rw [show b = a by linarith [h3]] at heq 
        have h7 : sqrt b = sqrt a := by 
          rw [show b = a by linarith [h3]]
        nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), 
          Real.sqrt_nonneg a, Real.sqrt_nonneg b, 
          Real.sq_sqrt (show 0 ≤ b by linarith), 
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
      have h7 : 4 * a ^ 2 + a = 4 * a * sqrt a := by 
        linarith [h6]
      have h8 : a * (4 * a - 4 * sqrt a + 1) = 0 := by 
        nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), 
          Real.sqrt_nonneg a, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg a)]
      cases (mul_eq_zero.mp h8) with 
      | inl ha1 =>
        have ha0 : a = 0 := by linarith
        have a0 : a = 0 := by linarith
        have b0 : b = 0 := by linarith [h3, a0]
        -- Let's prove the goals
        have ha1 : (a = 0 ∨ b = 1 / 4) := by 
          left 
          linarith 
        have ha2 : (b = 0 ∨ a = 1 / 4) := by 
          left 
          linarith 
        exact ⟨h3, ha1, ha2⟩
      | inr h9 =>
        have h9' : (sqrt a - 1 / 2) ^ 2 = 0 := by
          nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), 
            Real.sqrt_nonneg a, sq_nonneg (sqrt a - 1 / 2), 
            mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg a)]
        have h10 : sqrt a = 1 / 2 := by 
          nlinarith 
        have ha14 : a = 1 / 4 := by 
          have h11 : sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
          nlinarith [h10]
        have ha0 : (a = 0 ∨ b = 1 / 4) := by 
          right 
          nlinarith [h3, ha14] 
        have hb0 : (b = 0 ∨ a = 1 / 4) := by 
          right 
          nlinarith [h3, ha14] 
        exact ⟨h3, ha0, hb0⟩ 
    · -- Backward: a = b ∧ (a = 0 ∨ b = 1/4) ∧ (b = 0 ∨ a = 1/4) implies equality
      rintro ⟨h_eq, h1, h2⟩ 
      have h3 : a = b := h_eq 
      rcases h1 with (ha0 | hb14)
      · -- Case a = 0 
        have ha0 : a = 0 := ha0 
        have hb0 : b = 0 := by 
          linarith [ha0, h3] 
        simp [ha0, hb0, Real.sqrt_zero] 
      · -- Case b = 1/4 
        have hb14 : b = 1 / 4 := hb14 
        have ha14 : a = 1 / 4 := by 
          linarith [hb14, h3]
        have h6 : sqrt a = 1 / 2 := by 
          rw [show a = (1 / 4 : ℝ) by linarith [ha14]] 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h7 : sqrt b = 1 / 2 := by 
          rw [show b = (1 / 4 : ℝ) by linarith [hb14]]
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [show sqrt a = 1 / 2 by linarith [h6]]
        rw [show sqrt b = 1 / 2 by linarith [h7]]
        rw [show a = 1 / 4 by linarith [ha14]]
        rw [show b = 1 / 4 by linarith [hb14]]
        norm_num