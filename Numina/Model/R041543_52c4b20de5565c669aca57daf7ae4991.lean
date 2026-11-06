import Mathlib

theorem algebra_275809 {p q : ℝ} (h : ∃ x1 x2, x1^2 + p * x1 + q = 0 ∧ x2^2 + p * x2 + q = 0) :
    {x : ℝ | x^4 - (p^2 - 2 * q) * x^2 + q^2 = 0} =
    {x : ℝ | ∃ x1 x2 : ℝ, x1^2 + p * x1 + q = 0 ∧ x2^2 + p * x2 + q = 0 ∧ (x = x1 ∨ x = x2 ∨ x = -x1 ∨ x = -x2)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First direction: if `x` is a solution to the degree 4 equation, it's either a root of the quadratic or its negative
    intro h4
    have h4' : (x ^ 2 + p * x + q) * (x ^ 2 - p * x + q) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - p * x), sq_nonneg (x ^ 2 + p * x), sq_nonneg (x ^ 2), sq_nonneg ((x * (p))), sq_nonneg ((x)), sq_nonneg (p), sq_nonneg (q)]
    cases' (mul_eq_zero.mp h4') with h5 h6
    · -- Case where x^2 + p * x + q = 0
      rcases h with ⟨x1, x2, hx1, hx2⟩
      use x, x
      constructor
      · -- Show x^2 + p * x + q = 0
        linarith
      constructor
      · -- Show x^2 + p * x + q = 0
        linarith
      · -- Show x = x ∨ x = x ∨ x = -x ∨ x = -x
        simp
    · -- Case where x^2 - p * x + q = 0
      rcases h with ⟨x1, x2, hx1, hx2⟩
      use -x, -x
      constructor
      · -- Show (-x)^2 + p * (-x) + q = 0
        nlinarith
      constructor
      · -- Show (-x)^2 + p * (-x) + q = 0
        nlinarith
      · -- Show x = -x ∨ x = -x ∨ x = -(-x) ∨ x = -(-x)
        simp
  · -- Second direction: if `x` is x1, x2, -x1, -x2, then it's a solution to the degree 4 equation
    intro h
    rcases h with ⟨x1, x2, hx1, hx2, h⟩
    rcases h with (r | r | r | r)
    · -- When x = x1
      rw [r]
      have ht4 : x1 ^ 4 - (p ^ 2 - 2 * q) * x1 ^ 2 + q ^ 2 = 0 := by
        have h11 : x1 ^ 2 + p * x1 + q = 0 := hx1
        nlinarith [sq_nonneg (x1 ^ 2 - p * x1 + q), sq_nonneg (x1 + p / 2), sq_nonneg (p), sq_nonneg (q)]
      assumption
    · -- When x = x2
      rw [r]
      have ht4 : x2 ^ 4 - (p ^ 2 - 2 * q) * x2 ^ 2 + q ^ 2 = 0 := by
        have h22 : x2 ^ 2 + p * x2 + q = 0 := hx2
        nlinarith [sq_nonneg (x2 ^ 2 - p * x2 + q), sq_nonneg (x2 + p / 2), sq_nonneg (p), sq_nonneg (q)]
      assumption
    · -- When x = -x1
      rw [r]
      have ht4 : (-x1) ^ 4 - (p ^ 2 - 2 * q) * (-x1) ^ 2 + q ^ 2 = 0 := by
        have h11 : x1 ^ 2 + p * x1 + q = 0 := hx1
        nlinarith [sq_nonneg (x1 ^ 2 - p * x1 + q), sq_nonneg (x1 + p / 2), sq_nonneg (p), sq_nonneg (q)]
      assumption
    · -- When x = -x2
      rw [r]
      have ht4 : (-x2) ^ 4 - (p ^ 2 - 2 * q) * (-x2) ^ 2 + q ^ 2 = 0 := by
        have h22 : x2 ^ 2 + p * x2 + q = 0 := hx2
        nlinarith [sq_nonneg (x2 ^ 2 - p * x2 + q), sq_nonneg (x2 + p / 2), sq_nonneg (p), sq_nonneg (q)]
      assumption