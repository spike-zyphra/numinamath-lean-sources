import Mathlib

theorem algebra_13757 {x : ℝ} (hx : x * 108 = 200) : ⌊x * 100 + 1 / 2⌋ / 100 = (1.85 : ℝ) := by
  have hx_val : x = (200 : ℝ) / 108 := by
    linarith
  rw [hx_val]
  norm_num
  <;> ring_nf <;> norm_num