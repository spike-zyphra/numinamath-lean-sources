import Mathlib

theorem algebra_166122 (x y : ℝ) (h1 : x^2 + y^4 = 20) (h2 : x^4 + y^2 = 20) :
    (x = 2 ∧ y = 2) ∨ (x = -2 ∧ y = -2) ∨ (x = 2 ∧ y = -2) ∨ (x = -2 ∧ y = 2) := by
  have h4 : (x - 2) ^ 2 * (x + 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4), sq_nonneg (x^2 - y^2), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (y^2 - 2), sq_nonneg (x^2 - 2), sq_nonneg (x ^ 2 - y ^ 2)]
  have h5 : (x - 2) ^ 2 = 0 ∨ (x + 2) ^ 2 = 0 := by
    cases (mul_eq_zero.mp h4) with
    | inl h7 => 
      left
      linarith
    | inr h8 => 
      right
      linarith
  cases h5 with
  | inl h6 => 
    have hx : x = 2 := by 
      nlinarith [pow_eq_zero h6]
    have h6 : y ^ 4 = 16 := by
      nlinarith [h1, hx]
    have h7 : y ^ 2 = 4 ∨ y ^ 2 = -4 := by 
      have h6 : y ^ 4 = 16 := by
        nlinarith [h1, hx]
      have h9 : y^4 - 16 = 0 := by 
        linarith
      have h10 : (y^2 - 4) * (y^2 + 4) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp h10) with h11 h12
      · left
        linarith
      · right
        linarith
    cases h7 with
    | inl h7 => 
      have h8 : y ^ 2 = 4 := by linarith
      have h9 : y = 2 ∨ y = -2 := by 
        have h9 : y^2 = 4 := h8
        have : y = 2 ∨ y = -2 := by 
          have h10 : y ^ 2 - 4 = 0 := by 
            linarith
          have h11 : (y - 2) * (y + 2) = 0 := by 
            nlinarith
          cases' (mul_eq_zero.mp h11) with h12 h13
          · left
            linarith
          · right
            linarith
        assumption
      cases h9 with
      | inl h9 => 
        left
        constructor
        · linarith
        · linarith
      | inr h9 => 
        right
        right
        left
        constructor
        · linarith
        · linarith
    | inr h7 => 
      nlinarith [sq_nonneg (y ^ 2)]
  | inr h6 => 
    have hx : x = -2 := by 
      nlinarith [pow_eq_zero h6]
    have h6 : y ^ 4 = 16 := by
      nlinarith [h1, hx]
    have h7 : y ^ 2 = 4 ∨ y ^ 2 = -4 := by 
      have h6 : y ^ 4 = 16 := by
        nlinarith [h1, hx]
      have h9 : y^4 - 16 = 0 := by 
        linarith
      have h10 : (y^2 - 4) * (y^2 + 4) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp h10) with h11 h12
      · left
        linarith
      · right
        linarith
    cases h7 with
    | inl h7 => 
      have h8 : y ^ 2 = 4 := by linarith
      have h9 : y = 2 ∨ y = -2 := by 
        have h9 : y^2 = 4 := h8
        have : y = 2 ∨ y = -2 := by 
          have h10 : y ^ 2 - 4 = 0 := by 
            linarith
          have h11 : (y - 2) * (y + 2) = 0 := by 
            nlinarith
          cases' (mul_eq_zero.mp h11) with h12 h13
          · left
            linarith
          · right
            linarith
        assumption
      cases h9 with
      | inl h9 => 
        right
        right
        right
        constructor
        · linarith
        · linarith
      | inr h9 => 
        right
        left
        constructor
        · linarith
        · linarith
    | inr h7 => 
      nlinarith [sq_nonneg (y ^ 2)]