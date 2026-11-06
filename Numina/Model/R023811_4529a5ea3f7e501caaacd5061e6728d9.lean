import Mathlib

theorem algebra_320949 (x : ℝ) :
    ((x^2 + x + 1)^3 - (x^2 + 1)^3 - x^3) *
    ((x^2 - x + 1)^3 - (x^2 + 1)^3 + x^3) =
    3 * ((x^4 + x^2 + 1)^3 - (x^4 + 1)^3 - x^8) ↔
    x = 0 ∨ x^2 + x + 1 = 0 ∨ x^2 - x + 1 = 0 ∨ (x^2 + 1)^2 = x^4 + 1 := by
  constructor
  · -- Forward implication: equation implies the roots.
    intro h
    have eq1 : ((x^2 + x + 1)^3 - (x^2 + 1)^3 - x^3) * ((x^2 - x + 1)^3 - (x^2 + 1)^3 + x^3) - 3 * ((x^4 + x^2 + 1)^3 - (x^4 + 1)^3 - x^8) = 0 := by 
      linarith
    have eq2 : x^3 * (x^6 + 3*x^4 + 2*x^3 + 3*x^2 + 1) = 0 := by
      nlinarith [sq_nonneg (x^3), sq_nonneg (x^2 - x), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x^2), sq_nonneg ((x^2 + x + 1) ^ 2), sq_nonneg ((x^2 - x + 1) ^ 2)]
    cases (mul_eq_zero.mp eq2) with 
    | inl h3 =>
      have h4 : x = 0 := by
        have h5 : x^3 = 0 := by
          linarith
        have : x = 0 := by
          have h6 : x^3 = 0 := h5
          simp at h6 ⊢
          <;> nlinarith
        linarith
      left
      exact_mod_cast h4
    | inr h4 =>
      have eq3 : (x^2 + x + 1) * (x^2 - x + 1) * (x^2 + 1) = 0 := by
        nlinarith [sq_nonneg (x^3), sq_nonneg (x^2 - x), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x^2), sq_nonneg (x^2 + 1)]
      cases (mul_eq_zero.mp eq3) with
      | inl eq4 =>
        cases (mul_eq_zero.mp eq4) with 
        | inl eq5 =>
          right
          left
          linarith
        | inr eq5 =>
          right
          right
          left
          linarith
      | inr eq6 =>
        have eq7 : x^2 + 1 = 0 := by
          nlinarith
        right
        right
        right
        nlinarith [sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num), sq_nonneg (x^2 + 1)]
  · -- Backward implications: roots satisfy the equation
    rintro (h | h | h | h)
    · -- Case x = 0 
      rw [h]
      norm_num
    · -- Case x^2 + x + 1 = 0 
      have eq1 : x^2 = -x - 1 := by
        nlinarith 
      have eq2 : x^3 = 1 := by 
        nlinarith [sq_nonneg (x^2 + x + 1), sq_nonneg (x^2 - x +1), sq_nonneg (x^2 + 1)]
      have eq3 : x^4 = x := by 
        calc 
          x^4 = (x^2)^2 := by ring_nf
          _ = (-x - 1)^2 := by rw [eq1]
          _ = x^2 + 2*x + 1 := by ring_nf
          _ = (-x - 1) + 2*x + 1 := by rw [eq1]
          _ = x := by ring_nf
      have eq4 : ((x^2 + x + 1)^3 - (x^2 + 1)^3 - x^3) * ((x^2 - x + 1)^3 - (x^2 + 1)^3 + x^3) = 3 * ((x^4 + x^2 + 1)^3 - (x^4 + 1)^3 - x^8) := by 
        simp [eq1, eq2, eq3, pow_two, pow_three, pow_succ, mul_add, mul_sub]
        <;> nlinarith 
      linarith 
    · -- Case x^2 - x + 1 = 0 
      have eq1 : x^2 = x - 1 := by 
        nlinarith 
      have eq2 : x^3 = -1 := by 
        nlinarith [sq_nonneg (x^2 + x + 1), sq_nonneg (x^2 - x +1), sq_nonneg (x^2 + 1)]
      have eq3 : x^4 = -x := by 
        calc 
          x^4 = (x^2) ^ 2 := by ring_nf
          _ = (x - 1) ^ 2 := by rw [eq1]
          _ = x^2 - 2*x + 1 := by ring_nf
          _ = (x - 1) - 2*x + 1 := by rw [eq1]
          _ = -x := by ring_nf
      have eq4 : ((x^2 + x + 1)^3 - (x^2 + 1)^3 - x^3) * ((x^2 - x + 1)^3 - (x^2 + 1)^3 + x^3) = 3 * ((x^4 + x^2 + 1)^3 - (x^4 + 1)^3 - x^8) := by 
        simp [eq1, eq2, eq3, pow_two, pow_three, pow_succ, mul_add, mul_sub]
        <;> nlinarith 
      linarith 
    · -- Case (x^2 + 1)^2 = x^4 + 1 
      have eq1 : x^4 - 2 * x^2 = 0 := by 
        nlinarith [h]
      have eq2 : x^2 * (x^2 - 2) = 0 := by
        linarith 
      have eq3 : x^2 = 0 ∨ x^2 = 2 := by 
        cases (mul_eq_zero.mp eq2) with 
        | inl eq4 => 
          left 
          linarith 
        | inr eq4 => 
          right 
          linarith 
      cases eq3 with
      | inl eq4 => 
        have eq5 : x = 0 := by 
          nlinarith 
        rw [eq5] 
        norm_num 
      | inr eq4 => 
        have eq5 : x^2 = 2 := by 
          linarith 
        have eq6 : ((x^2 + x + 1)^3 - (x^2 + 1)^3 - x^3) * ((x^2 - x + 1)^3 - (x^2 + 1)^3 + x^3) = 3 * ((x^4 + x^2 + 1)^3 - (x^4 + 1)^3 - x^8) := by
          rw [eq5] 
          nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg x), sq_nonneg (x^2), sq_nonneg (x^3), sq_nonneg (x^4)]
        linarith [eq6]