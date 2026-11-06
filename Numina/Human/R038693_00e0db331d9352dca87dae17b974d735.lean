import Mathlib
/-Solve the equation in ℝ
(x^2 - 3)^3 - (4 * x + 6)^3 + 6^3 = 18 * (4 * x + 6) * (3 - x^2)-/
theorem algebra_249352 (x : ℝ) :
    (x^2 - 3)^3 - (4 * x + 6)^3 + 6^3 = 18 * (4 * x + 6) * (3 - x^2) ↔
    x = 2 + Real.sqrt 7 ∨ x = 2 - Real.sqrt 7 ∨ x = -3 := by 
  constructor
  · -- First direction: the equation implies the three solutions
    intro h 
    have h1 : (x^2 - 3) ^ 3 - (4 * x + 6) ^ 3 + (6 : ℝ) ^ 3 - 18 * (4 * x + 6) * (3 - x^2) = 0 := by linarith
    have h2 : (x^2 - 4 * x - 3) * (x + 3) ^ 2 * (x^2 - 2 * x + 13) = 0 := by 
      ring_nf at h1 ⊢
      nlinarith [sq_nonneg (x^2 - 4 * x - 3), sq_nonneg (x + 3), sq_nonneg (x^2 - 2 * x + 13)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · cases' (mul_eq_zero.mp h3) with h5 h6
      · -- Case x^2 - 4x - 3 = 0
        have h7 : x^2 - 4 * x - 3 = 0 := by linarith
        have h8 : x^2 - 4 * x - 3 = (x - (2 + Real.sqrt 7)) * (x - (2 - Real.sqrt 7)) := by
          ring_nf 
          rw [Real.sq_sqrt (by norm_num)]
          ring
        rw [h8] at h7
        cases' (mul_eq_zero.mp h7) with h9 h10
        · -- x - (2 + sqrt 7) = 0
          left
          linarith
        · -- x - (2 - sqrt 7) = 0
          right
          left
          linarith
      · -- Case (x + 3) ^ 2 = 0 
        have h11 : x + 3 = 0 := by 
          apply pow_eq_zero 
          exact h6
        right
        right
        linarith
    · -- Case x^2 - 2x + 13 = 0 
      have h12 : x^2 - 2 * x + 13 = 0 := by linarith
      have h13 : x^2 - 2 * x + 13 > 0 := by 
        nlinarith [sq_nonneg (x - 1)]
      linarith
  · -- Second direction: each solution satisfies the equation
    rintro (h | h | h)
    · -- x = 2 + sqrt 7 
      have h1 : x = 2 + Real.sqrt 7 := h
      have h2 : x^2 = 4 * x + 3 := by 
        have h3 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)
        rw [h1]
        ring_nf
        nlinarith [h3]
      have h3 : (x^2 - 3) ^ 3 - (4 * x + 6) ^ 3 + (6 : ℝ) ^ 3 = 18 * (4 * x + 6) * (3 - x^2) := by
        have h4 : x^2 - 3 = 4 * x := by linarith [h2]
        nlinarith [sq_nonneg (x^2 - 4 * x - 3), sq_nonneg (x + 3), sq_nonneg (x^2 - 2 * x + 13)]
      linarith
    · -- x = 2 - sqrt 7 
      have h1 : x = 2 - Real.sqrt 7 := h
      have h2 : x^2 = 4 * x + 3 := by 
        have h3 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)
        rw [h1]
        ring_nf
        nlinarith [h3, Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num : (0 : ℝ) < 7)]
      have h3 : (x^2 - 3) ^ 3 - (4 * x + 6) ^ 3 + (6 : ℝ) ^ 3 = 18 * (4 * x + 6) * (3 - x^2) := by
        have h4 : x^2 - 3 = 4 * x := by linarith [h2]
        nlinarith [sq_nonneg (x^2 - 4 * x - 3), sq_nonneg (x + 3), sq_nonneg (x^2 - 2 * x + 13)]
      linarith
    · -- x = -3 
      rw [h]
      norm_num