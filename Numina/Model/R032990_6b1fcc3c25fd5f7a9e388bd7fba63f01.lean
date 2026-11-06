import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_261178 {f : ℝ → ℝ} (hf : f = λ x => 0.5 * (x - 1 / 2) ^ 2)
  (M : ℝ × ℝ) (hM : M.1 = 0) (hM' : ∃ x y, x ≠ 0 ∧ y ≠ 0 ∧ f x = y ∧ f (-x) = -y ∧
  arctan (deriv f x) - arctan (deriv f (-x)) = π / 4) :
  M.2 = 0 ∨ M.2 = -3 := by
  rcases hM' with ⟨x, y, hx1, hy1, hx2, hx3, h⟩
  have hx4 : f x = 0.5 * (x - 1 / 2) ^ 2 := by rw [hf]
  have hx5 : f (-x) = 0.5 * (-x - 1 / 2) ^ 2 := by rw [hf]
  rw [hx4] at hx2
  rw [hx5] at hx3
  have h3 : 0.5 * (x - 1 / 2) ^ 2 + 0.5 * (-x - 1 / 2) ^ 2 = 0 := by
    nlinarith [hx2, hx3]
  have h4 : x ^ 2 + 1 / 4 = 0 := by
    ring_nf at h3
    nlinarith
  have h5 : x ^ 2 + 1 / 4 > 0 := by
    nlinarith [sq_nonneg x, sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num)]
  linarith -- This will derive False from h4 and h5