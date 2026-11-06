import Mathlib

theorem algebra_21227 : IsGreatest {x ^ 3 * y + y ^ 3 * z + z ^ 3 * x | (x : ℝ) (y : ℝ) (z : ℝ) (h₁ : x + y + z = 0) (h₂ : x * y * z = 2)} (-9) := by
  constructor
  · -- Show that -9 is in the set.
    use -1, -1, 2
    norm_num
  · -- Show that for any element in the set, it's less or equal to -9.
    intro w hw
    rcases hw with ⟨x, y, z, h₁, h₂, hw⟩
    have h3 : z = -x - y := by linarith
    rw [h3] at hw h₂
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg ((-x - y) + 1), sq_nonneg (x - y), sq_nonneg (y - (-x - y)), sq_nonneg (x - (-x - y)), sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x + y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg ((-x - y) - 1)]