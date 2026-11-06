import Mathlib

theorem algebra_187330 {x y : ℝ} (h1 : 0 ≤ (x + y) / 2) (h2 : 0 ≤ (x - y) / 3)
    (h3 : 0 ≤ (x + y) / 8) (h4 : 0 ≤ (x - y) / 12) (h5 : Real.sqrt ((x + y) / 2) +
    Real.sqrt ((x - y) / 3) = 14) (h6 : Real.sqrt ((x + y) / 8) - Real.sqrt ((x - y) / 12) = 3) :
    x = 124 ∧ y = 76 := by
  have ha : Real.sqrt ((x + y) / 8) = (1 / 2) * Real.sqrt ((x + y) / 2) := by
    have h7 : (x + y) / 8 = ((x + y) / 2) * (1 / 4) := by ring_nf
    rw [h7]
    have h8 : 0 ≤ (x + y) / 2 := h1
    have h9 : Real.sqrt (((x + y) / 2) * (1 / 4)) = Real.sqrt ((x + y) / 2) * Real.sqrt (1 / 4) := by
      rw [Real.sqrt_mul (by linarith)]
      all_goals norm_num
      all_goals linarith
    have h10 : Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h9, h10]
    all_goals ring_nf
    all_goals norm_num
    all_goals linarith
  have hb : Real.sqrt ((x - y) / 12) = (1 / 2) * Real.sqrt ((x - y) / 3) := by
    have h9 : (x - y) / 12 = ((x - y) / 3) * (1 / 4) := by ring_nf
    rw [h9]
    have h8 : 0 ≤ (x - y) / 3 := h2
    have h9 : Real.sqrt (((x - y) / 3) * (1 / 4)) = Real.sqrt ((x - y) / 3) * Real.sqrt (1 / 4) := by
      rw [Real.sqrt_mul (by linarith)]
      all_goals norm_num
      all_goals linarith
    have h10 : Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h9, h10]
    all_goals ring_nf
    all_goals norm_num
    all_goals linarith
  rw [ha] at h6
  rw [hb] at h6
  have h8 : Real.sqrt ((x + y) / 2) = 10 := by
    nlinarith
  have h9 : (x + y) / 2 = 100 := by
    calc
      (x + y) / 2 = (Real.sqrt ((x + y) / 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith [h1]
      _ = (10 : ℝ) ^ 2 := by
        rw [h8]
      _ = (100 : ℝ) := by
        norm_num
  have h10 : x + y = 200 := by
    linarith
  have h11 : Real.sqrt ((x - y) / 3) = 4 := by
    nlinarith
  have h12 : (x - y) / 3 = 16 := by
    calc
      (x - y) / 3 = (Real.sqrt ((x - y) / 3)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith [h2]
      _ = (4 : ℝ) ^ 2 := by
        rw [h11]
      _ = (16 : ℝ) := by
        norm_num
  have h13 : x - y = 48 := by
    linarith
  have hx : x = 124 := by
    linarith [h10, h13]
  have hy : y = 76 := by
    linarith [h10, hx]
  exact ⟨hx, hy⟩