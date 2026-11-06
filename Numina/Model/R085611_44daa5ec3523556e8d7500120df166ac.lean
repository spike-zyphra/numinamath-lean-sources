import Mathlib

theorem algebra_169959 (x : ℝ) (hx : 0 ≤ 36 + x^2) :
    12 * x = Real.sqrt (36 + x^2) * (6 + x - Real.sqrt (36 + x^2)) ↔ x = -6 ∨ x = 0 := by
  constructor
  · -- Forward direction: If the equation holds, then x = -6 or x = 0
    intro h
    have h1 : Real.sqrt (36 + x^2) ≥ 0 := by positivity
    have h2 : Real.sqrt (36 + x^2) ^ 2 = 36 + x^2 := by
      rw [Real.sq_sqrt]
      linarith
    have eq1 : Real.sqrt (36 + x^2) ^ 2 - (6 + x) * Real.sqrt (36 + x^2) + 12 * x = 0 := by
      nlinarith [h, h2]
    have eq2 : (x + 6) * (x + 6 - Real.sqrt (36 + x^2)) = 0 := by
      nlinarith [eq1, h2]
    cases' (mul_eq_zero.mp eq2) with h3 h4
    · -- Case where x + 6 = 0
      left
      linarith
    · -- Case where x + 6 - Real.sqrt (36 + x^2) = 0
      have h5 : Real.sqrt (36 + x^2) = x + 6 := by linarith
      have h6 : Real.sqrt (36 + x^2) ^ 2 = (x + 6) ^ 2 := by
        rw [h5]
      have h7 : 36 + x^2 = (x + 6) ^ 2 := by
        nlinarith [h2, h6]
      have h8 : 12 * x = 0 := by
        nlinarith
      have h9 : x = 0 := by
        linarith
      right
      exact h9
  · -- Backward direction: If x = -6 or x = 0, then the equation holds
    rintro (h | h)
    · -- Case where x = -6
      rw [h]
      have h1 : Real.sqrt (36 + (-6 : ℝ) ^ 2) = 6 * Real.sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
        <;> ring_nf
      rw [h1]
      ring_nf
      <;> norm_num [Real.sq_sqrt]
      <;> linarith
    · -- Case where x = 0
      rw [h]
      have h1 : Real.sqrt (36 + (0 : ℝ) ^ 2) = 6 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      norm_num