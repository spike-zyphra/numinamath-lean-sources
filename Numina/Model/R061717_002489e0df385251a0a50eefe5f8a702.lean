import Mathlib

theorem algebra_206801 {x : ℝ} (hx : x ≠ 49 ∧ x ≠ 50) :
    (x - 49)/50 + (x - 50)/49 = 49/(x - 50) + 50/(x - 49) ↔
    x = 0 ∨ x = 4901/99 ∨ x = 99 := by
  constructor
  · -- Assume the equation, prove the disjunction of solutions
    intro h_eq
    have hx1 : x ≠ 49 := hx.1
    have hx2 : x ≠ 50 := hx.2
    have h1 : x - 49 ≠ 0 := by
      intro h
      apply hx1
      linarith
    have h2 : x - 50 ≠ 0 := by
      intro h
      apply hx2
      linarith
    field_simp [(show (x - 49) ≠ 0 by exact h1), (show (x - 50) ≠ 0 by exact h2)] at h_eq
    ring_nf at h_eq
    have h3 : x * (x - 99) * (99 * x - 4901) = 0 := by
      nlinarith [sq_nonneg (x), sq_nonneg (x - 4901 / 99), sq_nonneg (x - 99), sq_pos_of_ne_zero (show x - 49 ≠ 0 by exact h1), sq_pos_of_ne_zero (show x - 50 ≠ 0 by exact h2)]
    cases' (mul_eq_zero.mp h3) with h4 h5
    cases' (mul_eq_zero.mp h4) with h6 h7
    · -- Case x = 0
      left
      linarith
    · -- Case x - 99 = 0
      right
      right
      linarith
    · -- Case 99 * x - 4901 = 0
      right
      left
      linarith
  · -- Show that each of the given solutions satisfies the equation
    rintro (h_eq | h_eq | h_eq)
    · -- Case x = 0
      rw [h_eq]
      norm_num
    · -- Case x = 4901/99
      rw [h_eq]
      norm_num
    · -- Case x = 99
      rw [h_eq]
      norm_num