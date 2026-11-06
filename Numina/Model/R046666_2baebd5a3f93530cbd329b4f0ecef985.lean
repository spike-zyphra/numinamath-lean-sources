import Mathlib

open Real

lemma lemma_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 2) : a * b + b * c + c * a ≤ 4 / 3 := by
  have h1 : c = 2 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2 / 3), sq_nonneg (b - 2 / 3),
            sq_nonneg (a + b - 4/3), sq_nonneg (a - 2 + a + b), sq_nonneg (b - 2 + a + b),
            mul_pos ha hb]


theorem inequalities_261896 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 2) :
    27 / 13 ≤ 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) ∧
    (27 / 13 = 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) ↔ a = b ∧ b = c) := by

  constructor
  · -- Proof of inequality
    have h1 : a * b + b * c + c * a ≤ 4 / 3 := by
      apply lemma_1 a b c ha hb hc h
    have h2 : 0 < (1 + a * b) * (1 + b * c) * (1 + c * a) := by
      positivity
    have h3 : 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) - 27 / 13 ≥ 0 := by
      have h4 : 0 < (1 + a * b) * (1 + b * c) * (1 + c * a) := by
        positivity
      have h5 : 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) - 27 / 13 =
          ( (1 + b * c) * (1 + c * a) + (1 + a * b) * (1 + c * a) + (1 + a * b) * (1 + b * c) - (27 / 13) * ( (1 + a * b) * (1 + b * c) * (1 + c * a) ) ) / ( (1 + a * b) * (1 + b * c) * (1 + c * a) ) := by
        field_simp
        ring
      rw [h5]
      have h6 : (1 + b * c) * (1 + c * a) + (1 + a * b) * (1 + c * a) + (1 + a * b) * (1 + b * c) - (27 / 13) * ( (1 + a * b) * (1 + b * c) * (1 + c * a) ) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                  sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h1]
      have h7 : ( (1 + b * c) * (1 + c * a) + (1 + a * b) * (1 + c * a) + (1 + a * b) * (1 + b * c) - (27 / 13) * ( (1 + a * b) * (1 + b * c) * (1 + c * a) ) ) / ( (1 + a * b) * (1 + b * c) * (1 + c * a) ) ≥ 0 := by
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith
  · -- Proof of equality condition
    constructor
    · -- If 27/13 = ..., then a = b ∧ b = c
      intro h_eq
      have h1 : a * b + b * c + c * a = 4 / 3 := by
        have h2 : 0 < (1 + a * b) * (1 + b * c) * (1 + c * a) := by
          positivity
        have h3 : (1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a)) = 27 / 13 := by
          linarith
        have h4 : (1 + b * c) * (1 + c * a) + (1 + a * b) * (1 + c * a) + (1 + a * b) * (1 + b * c) = (27 / 13) * ( (1 + a * b) * (1 + b * c) * (1 + c * a) ) := by
          have h5 : 0 < (1 + a * b) * (1 + b * c) * (1 + c * a) := by
            positivity
          field_simp at h3 ⊢
          nlinarith
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                  sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h2 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h3 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have h4 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have h5 : a - b = 0 := by
        nlinarith
      have h6 : b - c = 0 := by
        nlinarith
      have h7 : a = b := by
        linarith
      have h8 : b = c := by
        linarith
      constructor
      · exact h7
      · exact h8
    · -- If a = b ∧ b = c, then 27/13 = ...
      rintro ⟨ha1, hb1⟩
      have h2 : a = c := by
        linarith
      have h3 : a = b := by
        linarith
      have h4 : b = c := by
        linarith
      have h12 : a = 2 / 3 := by
        have h13 : a + b + c = 2 := h
        rw [show b = a by linarith [h3], show c = a by linarith [h3, h4]] at h13
        nlinarith
      have h13 : a * b = 4 / 9 := by
        rw [show b = a by linarith [h3]]
        nlinarith [h12]
      have h14 : 1 / (1 + a * b) = 9 / 13 := by
        rw [h13]
        norm_num
      have h15 : 1 / (1 + b * c) = 9 / 13 := by
        have h16 : b * c = 4 / 9 := by
          rw [show c = a by linarith [h3, h4]]
          rw [show b = a by linarith [h3]]
          nlinarith [h12]
        rw [h16]
        norm_num
      have h17 : 1 / (1 + c * a) = 9 / 13 := by
        have h18 : c * a = 4 / 9 := by
          rw [show c = a by linarith [h3, h4]]
          rw [show a = a by rfl]
          nlinarith [h12]
        rw [h18]
        norm_num
      linarith