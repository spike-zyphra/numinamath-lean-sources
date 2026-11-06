import Mathlib

theorem algebra_246036 {x y n : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x / (4 * 64^7) + 1024^(-4 : ℤ) * x / 16 = 16)
    (hy' : y = (3^(4 + n) + 5 * 3^n) / (3^(3 + n) - 25 * 3^n)) :
    x^y = 2^2021 := by

  have eq1 : x = (2 : ℝ) ^ (47 : ℝ) := by
    have eq3 : x / (4 * (64 : ℝ) ^ 7) + (1024 : ℝ) ^ (-4 : ℤ) * x / 16 = 16 := h
    have eq4 : x / (4 * (64 : ℝ) ^ 7) = x / (2 ^ (44 : ℝ)) := by
      norm_num
    have eq5 : (1024 : ℝ) ^ (-4 : ℤ) * x / 16 = x / (2 ^ (44 : ℝ)) := by 
      have h7 : (1024 : ℝ) ^ (-4 : ℤ) = (2 : ℝ) ^ (-40 : ℝ) := by 
        norm_num
      rw [h7]
      field_simp
      <;> ring_nf
    have eq6 : x / (2 ^ (44 : ℝ)) + x / (2 ^ (44 : ℝ)) = 16 := by 
      have eq7 : x / (4 * (64 : ℝ) ^ 7) + (1024 : ℝ) ^ (-4 : ℤ) * x / 16 = 16 := h
      rw [eq4, eq5] at eq7 
      linarith 
    have eq7 : x / (2 ^ (44 : ℝ)) = 8 := by 
      linarith 
    have eq8 : x = (2 : ℝ) ^ (47 : ℝ) := by 
      have eq9 : x = 8 * (2 : ℝ) ^ (44 : ℝ) := by 
        have h11 : x / (2 : ℝ) ^ (44 : ℝ) = 8 := eq7
        field_simp at h11 ⊢
        <;> nlinarith 
      have eq10 : (8 * (2 : ℝ) ^ (44 : ℝ) ) = (2 : ℝ) ^ (47 : ℝ) := by 
        have h11 : (8 * (2 : ℝ) ^ (44 : ℝ) ) = (2 : ℝ) ^ (47 : ℝ) := by 
          have h12 : (2 : ℝ) ^ (47 : ℝ) = (2 : ℝ) ^ (44 : ℝ) * (2 : ℝ) ^ (3 : ℝ) := by 
            rw [← Real.rpow_add]
            norm_num
            all_goals norm_num 
          have h13 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by 
            norm_num 
          rw [h13] at *
          <;> nlinarith [h12] 
        exact h11 
      rw [eq9] 
      exact eq10 
    exact eq8 
  have eq2 : y = (43 : ℝ) := by 
    rw [hy']
    have h7 : (3 : ℝ) ^ (4 + n) = (81 : ℝ) * (3 : ℝ) ^ n := by
      calc
        (3 : ℝ) ^ (4 + n) = (3 : ℝ) ^ (4 : ℝ) * (3 : ℝ) ^ (n : ℝ) := by 
          rw [← Real.rpow_add]
          ring_nf 
          all_goals norm_num 
        _ = (81 : ℝ) * (3 : ℝ) ^ (n : ℝ) := by 
          norm_num 
    have h8 : (3 : ℝ) ^ (3 + n) = (27 : ℝ) * (3 : ℝ) ^ n := by 
      calc 
        (3 : ℝ) ^ (3 + n) = (3 : ℝ) ^ (3 : ℝ) * (3 : ℝ) ^ (n : ℝ) := by 
          rw [← Real.rpow_add]
          ring_nf 
          all_goals norm_num 
        _ = (27 : ℝ) * (3 : ℝ) ^ (n : ℝ) := by 
          norm_num 
    have eq3 : (3 : ℝ) ^ (4 + n) + 5 * (3 : ℝ) ^ n = (43 : ℝ) * ((3 : ℝ) ^ (3 + n) - 25 * (3 : ℝ) ^ n) := by 
      rw [h7, h8]
      have h13 : (81 : ℝ) * (3 : ℝ) ^ n + (5 : ℝ) * (3 : ℝ) ^ n = (43 : ℝ) * ((27 : ℝ) * (3 : ℝ) ^ n - (25 : ℝ) * (3 : ℝ) ^ n) := by 
        ring_nf 
      linarith 
    have h9 : (3 ^ (4 + n) + 5 * 3^n : ℝ) / (3 ^ (3 + n) - 25 * 3^n) = 43 := by 
      have h10 : (3 ^ (3 + n) - 25 * 3^n : ℝ) ≠ 0 := by 
        by_contra h11
        have eq3' : (3 : ℝ) ^ (4 + n) + 5 * (3 : ℝ) ^ n = (43 : ℝ) * ((3 : ℝ) ^ (3 + n) - 25 * (3 : ℝ) ^ n) := eq3
        rw [h11, mul_zero] at eq3'
        have h15 : (3 : ℝ) ^ (n : ℝ) > 0 := by positivity
        nlinarith 
      field_simp [h10] at *
      <;> nlinarith [eq3]
    linarith 
  rw [eq1, eq2]
  norm_num