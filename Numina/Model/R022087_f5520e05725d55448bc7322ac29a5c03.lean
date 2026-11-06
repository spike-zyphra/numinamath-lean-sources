import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_187533 (x : ℝ) (hx : 2*x+1 ≠ 0) :
    2*x-1 > 3/(2*x+1) ↔ (x ∈ Ioo (-1) (-1/2) ∨ x ∈ Ioi 1) := by
  constructor
  · -- Assume $2x - 1 > \frac{3}{2x + 1}$, prove $(x \in (-1, -1/2) \cup (1, \infty))$
    intro h
    have h1 : 2 * x + 1 ≠ 0 := hx
    by_cases h2 : (2 * x + 1) > 0
    · -- Case $2x + 1 > 0$, so $x > -1/2$
      have h3 : 2 * x - 1 > 3 / (2 * x + 1) := h
      have h4 : (2 * x - 1) * (2 * x + 1) > 3 := by
        have h5 : (2 * x + 1) > (0 : ℝ) := h2
        have h6 : (2 * x - 1) > 3 / (2 * x + 1) := h3
        have h7 : (2 * x - 1) * (2 * x + 1) > (3 / (2 * x + 1) ) * (2 * x + 1) := by
          apply mul_lt_mul_of_pos_right h6 (by linarith)
        have h8 : (3 / (2 * x + 1) ) * (2 * x + 1) = 3 := by
          field_simp [h1]
        linarith
      have h5 : 4 * x^2 > 4 := by
        nlinarith
      have h6 : x > 1 := by nlinarith
      right
      exact h6
    · -- So $2x + 1 ≤ 0$, i.e., $x ≤ -1/2$
      have h2' : (2 * x + 1) ≤ 0 := by nlinarith
      have h2ne : (2 * x + 1) ≠ 0 := h1
      have h2neg : (2 * x + 1) < 0 := by
        by_contra h
        push_neg at h
        have : (2 * x + 1) = 0 := by linarith
        contradiction
      have h3 : 2 * x - 1 > 3 / (2 * x + 1) := h
      have h4 : (2 * x - 1) * (2 * x + 1) < 3 := by
        have h5 : (2 * x + 1) < (0 : ℝ) := h2neg
        have h6 : (2 * x - 1) > 3 / (2 * x + 1) := h3
        have h7 : (2 * x - 1) * (2 * x + 1) < (3 / (2 * x + 1) ) * (2 * x + 1) := by
          apply mul_lt_mul_of_neg_right h6 (by nlinarith)
        have h8 : (3 / (2 * x + 1) ) * (2 * x + 1) = 3 := by
          field_simp [h1]
        linarith
      have h5 : 4 * x^2 < 4 := by
        nlinarith
      have h6 : -1 < x ∧ x < -1 / 2 := by
        constructor
        · -- Show -1 < x
          nlinarith
        · -- Show x < -1/2
          nlinarith
      left
      exact ⟨h6.1, h6.2⟩
  · -- Assume $x \in ((-1, -1/2) \cup (1, \infty))$, prove $2x - 1 > \frac 3 {2x + 1}$
    rintro (h | h)
    · -- Case $x \in (-1, -1/2)$
      rcases h with ⟨h1, h2⟩
      have h3 : (2 * x + 1) < 0 := by linarith
      have h4 : (2 * x - 1) > 3 / (2 * x + 1) := by
        have h5 : (2 * x + 1) < 0 := h3
        have h6 : (2 * x - 1) * (2 * x + 1) < 3 := by
          nlinarith [sq_pos_of_neg (show (2 * x + 1 : ℝ) < 0 by linarith), sq_nonneg (x^2 - 1)]
        have h7 : (3 / (2 * x + 1) ) = 3 / (2 * x + 1) := by rfl
        have h8 : (2 * x - 1) > (3 / (2 * x + 1) ) := by
          have h9 : (2 * x - 1) * (2 * x + 1) < 3 := h6
          have h10 : (3 / (2 * x + 1) ) * (2 * x + 1) = 3 := by
            field_simp [show (2 * x + 1) ≠ 0 by linarith]
          have h11 : (2 * x - 1) * (2 * x + 1) < (3 / (2 * x + 1) ) * (2 * x + 1) := by
            linarith
          have h12 : (2 * x + 1) < 0 := h5
          have h13 : (2 * x - 1) > (3 / (2 * x + 1) ) := by
            apply (mul_lt_mul_left_of_neg h12).mp
            linarith
          linarith
        linarith
      assumption
    · -- Case $x \in (1, \infty)$
      have h1 : x > 1 := h
      have h2 : (2 * x + 1) > 0 := by linarith
      have h3 : (2 * x - 1) > 3 / (2 * x + 1) := by
        have h5 : (2 * x + 1) > 0 := h2
        have h6 : (2 * x - 1) * (2 * x + 1) > 3 := by
          nlinarith [sq_pos_of_pos (show (2 * x + 1 : ℝ) > 0 by linarith), sq_nonneg (x^2 - 1)]
        have h7 : (3 / (2 * x + 1) ) = 3 / (2 * x + 1) := by rfl
        have h8 : (2 * x - 1) > (3 / (2 * x + 1) ) := by
          have h9 : (2 * x - 1) * (2 * x + 1) > 3 := h6
          have h10 : (3 / (2 * x + 1) ) * (2 * x + 1) = 3 := by
            field_simp [show (2 * x + 1) ≠ 0 by linarith]
          have h11 : (2 * x - 1) * (2 * x + 1) > (3 / (2 * x + 1) ) * (2 * x + 1) := by
            linarith
          have h12 : (2 * x + 1) > 0 := h5
          have h13 : (2 * x - 1) > (3 / (2 * x + 1) ) := by
            apply (mul_lt_mul_right h12).mp
            linarith
          linarith
        linarith
      assumption