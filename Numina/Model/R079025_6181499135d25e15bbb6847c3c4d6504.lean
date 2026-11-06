import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_216358 :
  IsLeast {z : ℝ | ∃ x y : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ 1 ∧ z = max (max (x * y) (x * y - x - y + 1)) (x + y - 2 * x * y)} (4 / 9) := by
  constructor
  · -- Show that 4/9 is in the set
    use 1 / 3, 1 / 3
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num [max_assoc, max_comm, max_left_comm]
    <;> norm_num
  · -- Show the minimality: If z is in the set, then 4/9 ≤ z
    rintro z hz
    rcases hz with ⟨x, y, hx0, hxy, hy1, heq⟩
    by_contra h
    push_neg at h
    have h1 : max (max (x * y) (x * y - x - y + 1)) (x + y - 2 * x * y) < (4 / 9 : ℝ) := by linarith [h, heq]
    have h2 : x * y < (4 / 9 : ℝ) := by
      have h11 : max (max (x * y) (x * y - x - y + 1)) (x + y - 2 * x * y) ≥ (x * y : ℝ) := by simp [max_le_iff, le_refl]
      linarith [h11, h1]
    have h3 : (x * y - x - y + 1 : ℝ) < (4 / 9 : ℝ) := by
      have h12 : max (max (x * y) (x * y - x - y + 1)) (x + y - 2 * x * y) ≥ (x * y - x - y + 1 : ℝ) := by simp [max_le_iff, le_refl]
      linarith [h12, h1]
    have h4 : (x + y - 2 * x * y : ℝ) < (4 / 9 : ℝ) := by
      have h13 : max (max (x * y) (x * y - x - y + 1)) (x + y - 2 * x * y) ≥ (x + y - 2 * x * y : ℝ) := by simp [max_le_iff, le_refl]
      linarith [h13, h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (x + y - 2 / 3), mul_nonneg (show 0 ≤ (x : ℝ) by linarith) (show 0 ≤ (y : ℝ) by linarith), mul_nonneg (show 0 ≤ (1 - y : ℝ) by linarith) (show 0 ≤ (1 - x : ℝ) by linarith)]