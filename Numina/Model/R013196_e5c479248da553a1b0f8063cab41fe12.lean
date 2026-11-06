import Mathlib

theorem algebra_101911 {a b c : ℝ} (h₀ : abs (a - b) = 1) (h₁ : abs (b - c) = 1)
    (h₂ : abs (c - a) = 2) (h₃ : a * b * c = 60) :
    a / (b * c) + b / (c * a) + c / (a * b) - 1 / a - 1 / b - 1 / c = 1 / 20 := by
  have h4 : (a - b) = 1 ∨ (a - b) = -1 := by
    cases eq_or_eq_neg_of_abs_eq h₀ with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith
  have h5 : (b - c) = 1 ∨ (b - c) = -1 := by
    cases eq_or_eq_neg_of_abs_eq h₁ with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith
  have h6 : (c - a) = 2 ∨ (c - a) = -2 := by
    cases eq_or_eq_neg_of_abs_eq h₂ with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith
  cases h4 with
  | inl h41 =>
    cases h5 with
    | inl h51 =>
      have h7 : a = b + 1 := by linarith
      have h8 : b = c + 1 := by linarith
      have h9 : a = c + 2 := by
        rw [show b = c + 1 by linarith [h8]] at h7
        linarith
      have h10 : c ≠ 0 := by
        by_contra h
        rw [h] at h₃
        nlinarith
      have h11 : a ≠ 0 := by
        by_contra h
        rw [h] at h₃
        nlinarith
      have h12 : b ≠ 0 := by
        by_contra h
        rw [h] at h₃
        nlinarith
      have h13 : a * b * c = 60 := h₃
      rw [show a = c + 2 by linarith [h9], show b = c + 1 by linarith [h8]] at h13
      have hc : c = 3 := by
        have h20 : (c + 2) * (c + 1) * c = 60 := by
          nlinarith
        have h21 : c ^ 3 + 3 * c ^ 2 + 2 * c - 60 = 0 := by
          nlinarith [sq_nonneg (c + 2), sq_nonneg (c + 1), sq_nonneg (c)]
        have h22 : (c - 3) * (c ^ 2 + 6 * c + 20) = 0 := by
          nlinarith [sq_nonneg (c ^ 2 + 6 * c + 20), sq_nonneg (c - 3)]
        cases (mul_eq_zero.mp h22) with
        | inl h23 =>
          linarith
        | inr h24 =>
          nlinarith [sq_nonneg (c + 3)]
      have h24 : c = 3 := hc
      have h25 : b = 4 := by
        rw [h24] at h8
        linarith
      have h26 : a = 5 := by
        rw [h24] at h9
        linarith
      rw [h26, h25, h24]
      norm_num
    | inr h52 =>
      have h7 : a = b + 1 := by linarith
      have h8 : b = c - 1 := by linarith
      have h9 : a = c := by
        rw [show b = c - 1 by linarith [h8]] at h7
        linarith
      have h10 : abs (c - a) = 2 := h₂
      rw [show c - a = 0 by linarith [h9]] at h10
      norm_num at h10
  | inr h42 =>
    cases h5 with
    | inl h51 =>
      have h7 : a = b - 1 := by linarith
      have h8 : b = c + 1 := by linarith
      have h9 : a = c := by
        rw [show b = c + 1 by linarith [h8]] at h7
        linarith
      have h10 : abs (c - a) = 2 := h₂
      rw [show c - a = 0 by linarith [h9]] at h10
      norm_num at h10
    | inr h52 =>
      have h7 : a = b - 1 := by linarith
      have h8 : b = c - 1 := by linarith
      have h9 : a = c - 2 := by
        rw [show b = c - 1 by linarith [h8]] at h7
        linarith
      have h10 : c ≠ 0 := by
        by_contra h
        rw [h] at h₃
        nlinarith
      have h11 : a ≠ 0 := by
        by_contra h
        rw [h] at h₃
        nlinarith
      have h12 : b ≠ 0 := by
        by_contra h
        rw [h] at h₃
        nlinarith
      have h13 : a * b * c = 60 := h₃
      rw [show a = c - 2 by linarith [h9], show b = c - 1 by linarith [h8]] at h13
      have hc : c = 5 := by
        have h20 : (c - 2) * (c - 1) * c = 60 := by
          nlinarith
        have h21 : c ^ 3 - 3 * c ^ 2 + 2 * c - 60 = 0 := by
          nlinarith [sq_nonneg (c - 2), sq_nonneg (c - 1), sq_nonneg (c)]
        have h22 : (c - 5) * (c ^ 2 + 2 * c + 12) = 0 := by
          nlinarith [sq_nonneg (c ^ 2 + 2 * c + 12), sq_nonneg (c - 5)]
        cases (mul_eq_zero.mp h22) with
        | inl h23 =>
          linarith
        | inr h24 =>
          nlinarith [sq_nonneg (c + 1)]
      have h24 : c = 5 := hc
      have h25 : b = 4 := by
        rw [h24] at h8
        linarith
      have h26 : a = 3 := by
        rw [h24] at h9
        linarith
      rw [h26, h25, h24]
      norm_num