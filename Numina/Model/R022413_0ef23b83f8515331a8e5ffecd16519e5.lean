import Mathlib

theorem algebra_213560 (x : ℝ) :
    3 * x - x ^ 2 + Real.sqrt ((9 - x ^ 2) * (6 * x - x ^ 2)) = 0 ↔
    x = 0 ∨ x = 3 := by
  constructor
  · -- Forward direction: Equation implies x = 0 or x = 3
    intro h
    by_cases h1 : (9 - x ^ 2) * (6 * x - x ^ 2) ≥ 0
    · -- If the square root is defined, then solve by squaring both sides
      have h2 : Real.sqrt ((9 - x ^ 2) * (6 * x - x ^ 2)) ≥ 0 := by
        apply Real.sqrt_nonneg
      have h3 : Real.sqrt ((9 - x ^ 2) * (6 * x - x ^ 2)) = x ^ 2 - 3 * x := by
        nlinarith [h, h2]
      have h4 : (Real.sqrt ((9 - x ^ 2) * (6 * x - x ^ 2))) ^ 2 = (x ^ 2 - 3 * x) ^ 2 := by
        rw [h3]
        <;> nlinarith
      have h5 : (Real.sqrt ((9 - x ^ 2) * (6 * x - x ^ 2))) ^ 2 = (9 - x ^ 2) * (6 * x - x ^ 2) := by
        rw [Real.sq_sqrt]
        linarith
      have h6 : (9 - x ^ 2) * (6 * x - x ^ 2) = (x ^ 2 - 3 * x) ^ 2 := by
        nlinarith [h4, h5]
      have h7 : x * (x - 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- x = 0 is one solution
        left
        linarith
      · -- x = 3 is the other solution
        right
        linarith
    · -- If the square root is not defined, then sqrt(...) = 0
      have h1a : Real.sqrt ((9 - x ^ 2) * (6 * x - x ^ 2)) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
        all_goals nlinarith
      rw [h1a] at h
      have h7 : x * (x - 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- x = 0 is one solution
        left
        linarith
      · -- x = 3 is the other solution
        right
        linarith
  · -- Backward direction: x = 0 or x = 3 implies the equation
    rintro (h | h)
    · -- Check x = 0
      rw [h]
      norm_num [Real.sqrt_eq_iff_sq_eq]
      <;> nlinarith
    · -- Check x = 3
      rw [h]
      norm_num [Real.sqrt_eq_iff_sq_eq]
      <;> nlinarith