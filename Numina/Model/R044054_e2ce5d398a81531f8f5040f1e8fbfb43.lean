import Mathlib

theorem algebra_93926 {N : ℝ} (hN : N > 1) : (N * (N * (N ^ (1 / 3 : ℝ))) ^ (1 / 3 : ℝ)) ^ (1 / 3 : ℝ) = N ^ ((13 : ℝ) / 27) := by
  have h3 : (N ^ (1 / 3 : ℝ)) > 0 := by
    apply Real.rpow_pos_of_pos
    linarith
  have h4 : (N * (N ^ (1 / 3 : ℝ)) ) = N ^ (4 / 3 : ℝ) := by
    have h5 : N ^ (4 / 3 : ℝ) = N ^ (1 : ℝ) * N ^ (1 / 3 : ℝ) := by
      rw [show (4 / 3 : ℝ) = 1 + (1 / 3 : ℝ) by norm_num]
      rw [Real.rpow_add]
      norm_num
      all_goals linarith
    rw [h5]
    have h6 : N ^ (1 : ℝ) = N := by
      simp
    rw [h6]
  have h7 : ((N * (N ^ (1 / 3 : ℝ)) ) ^ (1 / 3 : ℝ)) = N ^ (4 / 9 : ℝ) := by
    rw [h4]
    have h8 : (N ^ (4 / 3 : ℝ) ) ^ (1 / 3 : ℝ) = N ^ ( (4 / 3 : ℝ) * (1 / 3 : ℝ) ) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h8]
    all_goals norm_num
  have h9 : (N * ( (N * (N ^ (1 / 3 : ℝ)) ) ^ (1 / 3 : ℝ) ) ) = N ^ (13 / 9 : ℝ) := by
    rw [h7]
    have h10 : (N * (N ^ (4 / 9 : ℝ)) ) = N ^ (13 / 9 : ℝ) := by
      have h11 : N ^ (13 / 9 : ℝ) = N ^ (1 : ℝ) * N ^ (4 / 9 : ℝ) := by
        rw [show (13 / 9 : ℝ) = 1 + (4 / 9 : ℝ) by norm_num]
        rw [Real.rpow_add]
        norm_num
        all_goals linarith
      rw [h11]
      have h12 : N ^ (1 : ℝ) = N := by
        simp
      rw [h12]
    linarith [h10]
  rw [h9]
  have h11 : (N ^ (13 / 9 : ℝ)) ^ (1 / 3 : ℝ) = N ^ (13 / 27 : ℝ) := by
    rw [← Real.rpow_mul]
    norm_num
    all_goals linarith
  rw [h11]
  <;> ring_nf