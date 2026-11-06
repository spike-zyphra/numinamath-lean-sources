import Mathlib

theorem inequalities_253647 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x < 1 ∧ y < 1) :
    1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) ≥ 2 / (1 - x * y) := by
  rcases hxy with ⟨hx1, hy1⟩
  have h1 : 0 < 1 - x ^ 2 := by
    nlinarith [hx, hx1, sq_pos_of_pos hx]
  have h2 : 0 < 1 - y ^ 2 := by
    nlinarith [hy, hy1, sq_pos_of_pos hy]
  have h3 : 0 < 1 - x * y := by
    nlinarith [hx, hx1, hy, hy1, mul_pos hx hy]
  have h4 : 1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y) ≥ 0 := by
    have pos1 : 0 < (1 - x ^ 2) * (1 - y ^ 2) * (1 - x * y) := by positivity
    have h5 : 1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y) =
        ((1 - y ^ 2) * (1 - x * y) + (1 - x ^ 2) * (1 - x * y) - 2 * (1 - x ^ 2) * (1 - y ^ 2)) / ((1 - x ^ 2) * (1 - y ^ 2) * (1 - x * y)) := by
      field_simp [(show 1 - x ^ 2 ≠ 0 by linarith), (show 1 - y ^ 2 ≠ 0 by linarith), (show 1 - x * y ≠ 0 by linarith)]
      <;> ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1 / 2), sq_nonneg (x + y - 1), sq_nonneg (x * y - x * y), sq_nonneg (x - y), sq_nonneg (x * (y)), sq_nonneg ((1 - x) * (1 - y)), mul_pos hx hy, mul_pos (show 0 < 1 - x by linarith) (show 0 < 1 - y by linarith)]
    positivity
  linarith