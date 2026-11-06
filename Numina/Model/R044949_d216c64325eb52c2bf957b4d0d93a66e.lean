import Mathlib

theorem algebra_606264 : (∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ b ∨ b ≠ c ∧ ((c * (a ^ 3 + b ^ 3) = a * (b ^ 3 + c ^ 3)) ∧ (a * (b ^ 3 + c ^ 3) = b * (c ^ 3 + a ^ 3)))) ∧ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * (a ^ 3 + b ^ 3) = b * (b ^ 3 + c ^ 3) ∧ (b * (b ^ 3 + c ^ 3) = c * (c ^ 3 + a ^ 3)) → a = b ∧ b = c) := by
  constructor
  . use 1, 2, 2
    norm_num
  . intro a b c ⟨ha, hb, hc, h₁, h₂⟩
    have h1 : (a ^ 4 = b ^ 4) := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a ^ 3 - b ^ 3), sq_nonneg (b ^ 3 - c ^ 3), sq_nonneg (c ^ 3 - a ^ 3),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h2 : (b ^ 4 = c ^ 4) := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a ^ 3 - b ^ 3), sq_nonneg (b ^ 3 - c ^ 3), sq_nonneg (c ^ 3 - a ^ 3),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h6 : a = b := by
      have h7 : a ^ 4 = b ^ 4 := by linarith
      have h8 : a ^ 2 = b ^ 2 := by
        have h9 : a ^ 4 - b ^ 4 = 0 := by linarith
        have h10 : (a ^ 2 - b ^ 2) * (a ^ 2 + b ^ 2) = 0 := by
          ring_nf at h9 ⊢
          nlinarith
        cases' (mul_eq_zero.1 h10) with h11 h12
        · linarith
        · have h13 : a ^ 2 + b ^ 2 > 0 := by positivity
          have h14 : a ^ 2 + b ^ 2 = 0 := by nlinarith
          linarith
      have h18 : a ^ 2 = b ^ 2 := by linarith
      have h20 : (a - b) * (a + b) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h20) with h21 h22
      · linarith
      · have h24 : a + b > 0 := by positivity
        have h25 : a + b = 0 := by nlinarith
        linarith
    have h7 : b = c := by
      have h7 : b ^ 4 = c ^ 4 := by linarith
      have h8 : b ^ 2 = c ^ 2 := by
        have h9 : b ^ 4 - c ^ 4 = 0 := by linarith
        have h10 : (b ^ 2 - c ^ 2) * (b ^ 2 + c ^ 2) = 0 := by
          ring_nf at h9 ⊢
          nlinarith
        cases' (mul_eq_zero.1 h10) with h11 h12
        · linarith
        · have h13 : b ^ 2 + c ^ 2 > 0 := by positivity
          have h14 : b ^ 2 + c ^ 2 = 0 := by nlinarith
          linarith
      have h18 : b ^ 2 = c ^ 2 := by linarith
      have h20 : (b - c) * (b + c) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h20) with h21 h22
      · linarith
      · have h24 : b + c > 0 := by positivity
        have h25 : b + c = 0 := by nlinarith
        linarith
    constructor
    . linarith [h6]
    . linarith [h7]