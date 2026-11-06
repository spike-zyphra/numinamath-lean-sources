import Mathlib

theorem algebra_187173 (x : ℝ) : 2 * 4^(2 * x) - 17 * 4^x + 8 = (0 : ℝ) ↔
    x = 3 / 2 ∨ x = -1 / 2 := by
  constructor
  · -- Assume the equation, prove the two solutions
    intro h
    have h1 : (4 : ℝ) ^ (2 * x) = ((4 : ℝ) ^ x) ^ 2 := by
      calc
        (4 : ℝ) ^ (2 * x) = ((4 : ℝ) ^ x) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        _ = ((4 : ℝ) ^ x) ^ 2 := by norm_num
    have h2 : 2 * ((4 : ℝ) ^ x) ^ 2 - 17 * ((4 : ℝ) ^ x) + 8 = (0 : ℝ) := by
      have h1' : (4 : ℝ) ^ (2 * x) = ((4 : ℝ) ^ x) ^ 2 := h1
      rw [h1'] at h
      linarith
    have h3 : ((4 : ℝ) ^ x - 8) * ((4 : ℝ) ^ x - (1 / 2 : ℝ)) = (0 : ℝ) := by
      nlinarith [sq_nonneg ((4 : ℝ) ^ x - 8), sq_nonneg ((4 : ℝ) ^ x - (1 / 2 : ℝ)), Real.rpow_pos_of_pos (show (0 : ℝ) < (4 : ℝ) by norm_num) x]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case where 4^x - 8 = 0, so 4^x = 8
      have h6 : (4 : ℝ) ^ x = (8 : ℝ) := by
        linarith
      have eq1 : (4 : ℝ) ^ x = (2 : ℝ) ^ (2 * x : ℝ) := by
        calc
          (4 : ℝ) ^ x = ((2 : ℝ) ^ (2 : ℝ)) ^ x := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
          _ = (2 : ℝ) ^ (2 * x : ℝ) := by
            rw [← Real.rpow_mul]
            ring_nf
            all_goals norm_num
      have eq4 : (2 : ℝ) ^ (2 * x : ℝ) = (8 : ℝ) := by
        rw [eq1] at h6
        linarith
      have h9 : (2 : ℝ) ^ (2 * x : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by
        rw [eq4]
        norm_num
      have h10 : 2 * x = (3 : ℝ) := by
        have h11 : (2 * x : ℝ) = (3 : ℝ) := by
          apply_fun (Real.logb (2 : ℝ)) at h9
          have h12 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 * x : ℝ)) = (2 * x : ℝ) := by
            rw [Real.logb_rpow]
            all_goals norm_num
          have h13 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 : ℝ)) = (3 : ℝ) := by
            rw [Real.logb_rpow]
            all_goals norm_num
          rw [h12, h13] at h9
          linarith
        linarith
      have h7 : x = (3 / 2 : ℝ) := by
        linarith
      left
      linarith
    · -- Case where 4^x - 1/2 = 0, so 4^x = 1/2
      have h8 : (4 : ℝ) ^ x = (1 / 2 : ℝ) := by
        linarith
      have eq1 : (4 : ℝ) ^ x = (2 : ℝ) ^ (2 * x : ℝ) := by
        calc
          (4 : ℝ) ^ x = ((2 : ℝ) ^ (2 : ℝ)) ^ x := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
          _ = (2 : ℝ) ^ (2 * x : ℝ) := by
            rw [← Real.rpow_mul]
            ring_nf
            all_goals norm_num
      have eq4 : (2 : ℝ) ^ (2 * x : ℝ) = (1 / 2 : ℝ) := by
        rw [eq1] at h8
        linarith
      have h9 : (2 : ℝ) ^ (2 * x : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by
        rw [eq4]
        norm_num
      have h10 : 2 * x = (-1 : ℝ) := by
        have h11 : (2 * x : ℝ) = (-1 : ℝ) := by
          apply_fun (Real.logb (2 : ℝ)) at h9
          have h12 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 * x : ℝ)) = (2 * x : ℝ) := by
            rw [Real.logb_rpow]
            all_goals norm_num
          have h13 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (-1 : ℝ)) = (-1 : ℝ) := by
            rw [Real.logb_rpow]
            all_goals norm_num
          rw [h12, h13] at h9
          linarith
        linarith
      have h9 : x = (-1 / 2 : ℝ) := by
        linarith
      right
      linarith
  · -- Assume the solutions, prove the equation
    rintro (h | h)
    · -- Case where x = 3/2
      rw [h]
      have h11 : (4 : ℝ) ^ (3 / 2 : ℝ) = (8 : ℝ) := by
        have h12 : (4 : ℝ) ^ (3 / 2 : ℝ) = ((2 : ℝ) ^ (2 : ℝ)) ^ (3 / 2 : ℝ) := by
          norm_num
        have h13 : ((2 : ℝ) ^ (2 : ℝ)) ^ (3 / 2 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        have h14 : (2 : ℝ) ^ (3 : ℝ) = (8 : ℝ) := by
          norm_num
        rw [h12, h13, h14]
      have h12 : (4 : ℝ) ^ (2 * (3 / 2 : ℝ)) = (64 : ℝ) := by
        norm_num
        <;> norm_num [Real.rpow_natCast, Real.rpow_mul]
      rw [h11, h12]
      all_goals norm_num
    · -- Case where x = -1/2
      rw [h]
      have h11 : (4 : ℝ) ^ (-1 / 2 : ℝ) = (1 / 2 : ℝ) := by
        have h12 : (4 : ℝ) ^ (-1 / 2 : ℝ) = ((2 : ℝ) ^ (2 : ℝ)) ^ (-1 / 2 : ℝ) := by
          norm_num
        have h13 : ((2 : ℝ) ^ (2 : ℝ)) ^ (-1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        have h14 : (2 : ℝ) ^ (-1 : ℝ) = (1 / 2 : ℝ) := by
          norm_num
        rw [h12, h13, h14]
      have h12 : (4 : ℝ) ^ (2 * (-1 / 2 : ℝ)) = (1 / 4 : ℝ) := by
        norm_num
        <;> norm_num [Real.rpow_natCast, Real.rpow_mul]
      rw [h11, h12]
      all_goals norm_num