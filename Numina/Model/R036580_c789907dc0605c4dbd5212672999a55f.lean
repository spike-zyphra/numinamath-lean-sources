import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12457 :
  IsLeast {t : ℝ | ∃ x y, x > 1 ∧ y > 1 ∧ t = x ^ 2 / (y - 1) + y ^ 2 / (x - 1)} 8 := by 
  constructor
  · use 2, 2
    norm_num
  · -- Show that no value less than 8 is in the set
    intro t ht
    rcases ht with ⟨x, y, hx, hy, ht⟩
    have h1 : x - 1 > 0 := by linarith
    have h2 : y - 1 > 0 := by linarith
    have h3 : x ^ 2 / (y - 1) + y ^ 2 / (x - 1) ≥ 8 := by
      have h4 : x ^ 2 / (y - 1) + y ^ 2 / (x - 1) - (8 : ℝ) ≥ 0 := by 
        have h41 : 0 < (y - 1) * (x - 1) := by positivity
        have h42 : x ^ 2 / (y - 1) + y ^ 2 / (x - 1) - (8 : ℝ) =
            (x^2 * (x - 1) + y^2 * (y - 1) - 8 * (y - 1) * (x - 1)) / ((y - 1) * (x - 1)) := by 
          field_simp
          <;> ring
        rw [h42] at *
        apply div_nonneg
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2),
                  sq_nonneg (x * (x - 2)), sq_nonneg (y * (y - 2)),
                  mul_pos (show (0 : ℝ) < x - 1 by linarith) (show (0 : ℝ) < y - 1 by linarith),
                  sq_nonneg (x * (y - 2)), sq_nonneg (y * (x - 2)), 
                  sq_nonneg (x * y - 4)]
        positivity
      linarith
    linarith