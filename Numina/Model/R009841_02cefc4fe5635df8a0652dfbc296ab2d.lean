import Mathlib

open Real

theorem algebra_11094 (black white : ℝ)
    (hblack : black = π * 1 ^ 2 + π * (5 ^ 2 - 3 ^ 2)) (hwhite : white = π * (3^2 - 1^2) + π * (7^2 - 5^2)) :
    black / white = 17 / 32 := by
  have h1 : black = 17 * π := by
    rw [hblack]
    ring
  have h2 : white = 32 * π := by
    rw [hwhite]
    ring
  rw [h1, h2]
  have hpi : π ≠ 0 := by
    linarith [Real.pi_pos]
  field_simp [hpi]
  <;> ring_nf <;> field_simp [hpi] <;> linarith