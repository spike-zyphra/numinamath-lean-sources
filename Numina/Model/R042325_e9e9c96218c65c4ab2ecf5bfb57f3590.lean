import Mathlib

theorem algebra_610538{x y: ℝ}(xpos: 0 < x)(ypos: 0 < y)
  (h1: x^(√y) = 27)(h2: (√x)^y = 9):
  x*y = 16 * (3:ℝ)^(1/4:ℝ) := by

  have eq1 : (√y) * (Real.log x) = 3 * (Real.log 3) := by
    have h3 : Real.log ((x : ℝ) ^ (√y)) = Real.log (27 : ℝ) := by
      rw [h1]
    have h4 : Real.log ((x : ℝ) ^ (√y)) = (√y) * Real.log x := by
      rw [Real.log_rpow]
      all_goals linarith
    have h5 : Real.log (27 : ℝ) = 3 * (Real.log 3) := by
      calc
        Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ 3) := by norm_num
        _ = 3 * (Real.log 3) := by simp [Real.log_pow]
    rw [h4, h5] at h3
    linarith

  have eq2 : (y / 2) * (Real.log x) = 2 * (Real.log 3) := by
    have h6 : Real.log ((√x : ℝ) ^ y) = Real.log (9 : ℝ) := by
      rw [h2]
    have h7 : Real.log ((√x : ℝ) ^ y) = y * Real.log (√x) := by
      rw [Real.log_rpow]
      all_goals
        positivity
    have h8 : Real.log (√x) = (1 / 2) * Real.log x := by
      have h9 : Real.log (√x) = Real.log ((x) ^ (1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
      have h10 : Real.log ((x) ^ (1 / 2 : ℝ)) = (1 / 2) * Real.log x := by
        rw [Real.log_rpow]
        all_goals linarith
      rw [h9, h10]
    have h11 : Real.log (9 : ℝ) = 2 * (Real.log 3) := by
      calc
        Real.log (9 : ℝ) = Real.log ((3 : ℝ) ^ 2) := by norm_num
        _ = 2 * (Real.log 3) := by simp [Real.log_pow]
    rw [h7, h8, h11] at h6
    nlinarith

  have h12 : Real.log 3 > 0 := by
    apply Real.log_pos
    all_goals norm_num

  have eq3 : Real.log x = 9 / 4 * (Real.log 3) := by
    have eq5 : y * (Real.log x) ^ 2 = 9 * (Real.log 3) ^ 2 := by
      have h8 : ( (√y) * (Real.log x) ) ^ 2 = y * (Real.log x) ^ 2 := by
        calc
          ( (√y) * (Real.log x) ) ^ 2 = (√y) ^ 2 * (Real.log x) ^ 2 := by ring
          _ = y * (Real.log x) ^ 2 := by
            have h10 : (√y) ^ 2 = y := by
              rw [Real.sq_sqrt]
              linarith
            rw [h10]
      have h11 : ( (√y) * (Real.log x) ) ^ 2 = (3 * (Real.log 3)) ^ 2 := by
        rw [eq1]
      have h12 : (3 * (Real.log 3)) ^ 2 = 9 * (Real.log 3) ^ 2 := by
        nlinarith
      nlinarith [h12, h11, h8]
    have eq6 : y * (Real.log x) = 4 * (Real.log 3) := by
      nlinarith [eq2]
    have h13 : Real.log x ≠ 0 := by
      by_contra h
      rw [h] at eq1
      nlinarith [h12, eq1]

    have eq7' : Real.log x = 9 / 4 * Real.log 3 := by
      apply (mul_left_inj' (show Real.log 3 ≠ 0 by
        linarith [h12]
      )).mp
      nlinarith [eq5, eq6, h12]
    linarith

  have eq4 : Real.sqrt y = 4 / 3 := by
    have h14 : (√y) * (Real.log x) = 3 * (Real.log 3) := eq1
    rw [eq3] at h14
    nlinarith [h12]

  have eq5 : y = 16 / 9 := by
    have h15 : Real.sqrt y = 4 / 3 := eq4
    have h16 : y = (Real.sqrt y) ^ 2 := by
      rw [Real.sq_sqrt]
      all_goals linarith
    rw [h15] at h16
    nlinarith

  have eq9 : x = (3 : ℝ) ^ (9 / 4 : ℝ) := by
    have eq7' : Real.log x = 9 / 4 * Real.log 3 := eq3
    have eq8' : x = Real.exp (Real.log x) := by
      rw [Real.exp_log]
      linarith
    rw [eq8']
    rw [eq7']
    have h14 : Real.exp (9 / 4 * Real.log 3) = (3 : ℝ) ^ (9 / 4 : ℝ) := by
      have h16 : ( (3 : ℝ) ^ (9 / 4 : ℝ) ) = Real.exp ( (9 / 4 : ℝ) * Real.log (3 : ℝ) ) := by
        rw [Real.rpow_def_of_pos]
        field_simp [Real.log_exp]
        all_goals linarith
      linarith [h16]
    linarith [h14]

  have eq7 : x * y = 16 * (3 : ℝ) ^ (1 / 4 : ℝ) := by
    rw [eq9, eq5]
    have eq8 : (3 : ℝ) ^ (9 / 4 : ℝ) * (16 / 9) = 16 * (3 : ℝ) ^ (1 / 4 : ℝ) := by
      have eq9 : (3 : ℝ) ^ (9 / 4 : ℝ) = (3 : ℝ) ^ (2 + 1 / 4 : ℝ) := by norm_num
      have eq10 : (3 : ℝ) ^ (2 + 1 / 4 : ℝ) = (3 : ℝ) ^ (2 : ℝ) * (3 : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_add]
        norm_num
        all_goals norm_num
      have eq11 : (3 : ℝ) ^ (2 : ℝ) = 9 := by
        norm_num
      rw [eq9, eq10, eq11]
      all_goals
        ring_nf
        all_goals norm_num
    nlinarith [eq8]

  linarith [eq7]