import Mathlib

theorem inequalities_90852 (a b : ℝ) (ha : a > 4) (hb : b > 4) :
    ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1^2 + a * x1 + b = 0 ∧ x2^2 + a * x2 + b = 0 ∨
    ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1^2 + b * x1 + a = 0 ∧ x2^2 + b * x2 + a = 0 := by 
  by_cases h : a ^ 2 > 4 * b
  · -- If a^2 > 4*b, then the polynomial x^2 + a*x + b has two distinct roots
    use (-a + Real.sqrt (a ^ 2 - 4 * b)) / 2, (-a - Real.sqrt (a ^ 2 - 4 * b)) / 2
    left
    constructor
    · -- Show the two roots are different
      by_contra h1
      have h2 : Real.sqrt (a ^ 2 - 4 * b) = 0 := by
        nlinarith [Real.sqrt_nonneg (a ^ 2 - 4 * b)]
      have h3 : a ^ 2 - 4 * b = 0 := by
        rw [Real.sqrt_eq_zero (by nlinarith)] at h2
        linarith
      nlinarith
    constructor
    · -- Show (-a + Real.sqrt (a ^ 2 - 4 * b)) / 2 is a root
      field_simp
      nlinarith [Real.sqrt_nonneg (a ^ 2 - 4 * b), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 4 * b by nlinarith)]
    · -- Show (-a - Real.sqrt (a ^ 2 - 4 * b)) / 2 is a root
      field_simp
      nlinarith [Real.sqrt_nonneg (a ^ 2 - 4 * b), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 4 * b by nlinarith)]
  · -- If a^2 ≤ 4*b, check if b^2 > 4*a
    by_cases h' : b ^ 2 > 4 * a
    · -- If b^2 > 4*a, then the polynomial x^2 + b*x + a has two distinct roots
      use (-b + Real.sqrt (b ^ 2 - 4 * a)) / 2, (-b - Real.sqrt (b ^ 2 - 4 * a)) / 2
      right
      use (-b + Real.sqrt (b ^ 2 - 4 * a)) / 2, (-b - Real.sqrt (b ^ 2 - 4 * a)) / 2
      constructor
      · -- Show the two roots are different
        by_contra h1
        have h2 : Real.sqrt (b ^ 2 - 4 * a) = 0 := by
          nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a)]
        have h3 : b ^ 2 - 4 * a = 0 := by
          rw [Real.sqrt_eq_zero (by nlinarith)] at h2
          linarith
        nlinarith
      constructor
      · -- Show (-b + Real.sqrt (b ^ 2 - 4 * a)) / 2 is a root
        field_simp
        nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a), Real.sq_sqrt (show (0 : ℝ) ≤ b ^ 2 - 4 * a by nlinarith)]
      · -- Show (-b - Real.sqrt (b ^ 2 - 4 * a)) / 2 is a root
        field_simp
        nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a), Real.sq_sqrt (show (0 : ℝ) ≤ b ^ 2 - 4 * a by nlinarith)]
    · -- Both discriminants are non-positive
      exfalso
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 4), sq_nonneg (b - 4), 
                mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)]