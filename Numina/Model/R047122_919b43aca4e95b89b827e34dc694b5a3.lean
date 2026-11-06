import Mathlib

open Real

theorem inequalities_84103 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 3) :
    x * (x + y - z) ≤ 1 ∨ y * (y + z - x) ≤ 1 ∨ z * (z + x - y) ≤ 1 := by
  by_contra h1
  push_neg at h1
  rcases h1 with ⟨h1, h2, h3⟩
  have h4 : z = 3 - x - y := by linarith
  rw [h4] at h1 h2 h3
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - (3 - x - y)), sq_nonneg (x - (3 - x - y)), 
          mul_pos hx hy, mul_pos hx (show (3 - x - y : ℝ) > 0 by nlinarith), 
          mul_pos hy (show (3 - x - y : ℝ) > 0 by nlinarith)]