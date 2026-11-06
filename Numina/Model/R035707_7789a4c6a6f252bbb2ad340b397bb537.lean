import Mathlib

open Real

theorem inequalities_598755 (x : ℝ) (hx : 1 < x) :
    (1 / 3) * (x - 1) > x ^ ((1 : ℝ) / 3) - 1 := by
  have h1 : (1 / 3) * (x - 1) + 1 > x ^ ((1 : ℝ) / 3) := by
    have h2 : ( (1 / 3) * (x - 1) + 1 ) ^ 3 > x := by
      nlinarith [sq_pos_of_pos (show (0 : ℝ) < x - 1 by linarith), sq_nonneg (x - 1), sq_nonneg ((x : ℝ) + 8), sq_nonneg ((x : ℝ) - 4), mul_pos (show (0 : ℝ) < x - 1 by linarith) (show (0 : ℝ) < x - 1 by linarith)]
    have h3 : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h4 : ( (1 / 3) * (x - 1) + 1 ) > (x ^ ((1 : ℝ) / 3)) := by
      have h5 : ( (x ^ ((1 : ℝ) / 3)) ) ^ 3 = x := h3
      have h6 : ( ( (1 / 3) * (x - 1) + 1 ) ) ^ 3 > ( (x ^ ((1 : ℝ) / 3)) ) ^ 3 := by
        linarith [h2, h5]
      have h9 : ( ( (1 / 3) * (x - 1) + 1 ) ) > (x ^ ((1 : ℝ) / 3)) := by
        by_contra h
        push_neg at h
        have h11 : ( ( (1 / 3) * (x - 1) + 1 ) ) ≤ (x ^ ((1 : ℝ) / 3) ) := by linarith [h]
        have h12 : ( ( (1 / 3) * (x - 1) + 1 ) ) ^ 3 ≤ ( (x ^ ((1 : ℝ) / 3) ) ) ^ 3 := by
          nlinarith [sq_nonneg ( ( (1 / 3) * (x - 1) + 1 ) - x ^ ((1 : ℝ) / 3) ), sq_nonneg ( ( (1 / 3) * (x - 1) + 1 ) + x ^ ((1 : ℝ) / 3) ), sq_nonneg ( ( (1 / 3) * (x - 1) + 1 ) ), sq_nonneg (x ^ ((1 : ℝ) / 3) ), h11, sq_nonneg ( ( (1 / 3) * (x - 1) + 1 ) - x ^ ((1 : ℝ) / 3) ) ]
        linarith
      linarith
    linarith
  linarith [h1]