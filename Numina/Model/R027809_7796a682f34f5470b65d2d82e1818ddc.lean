import Mathlib

theorem algebra_361 (x y z : ℝ) (hx : x = Real.sqrt 7) (hy : y = 17 ^ ((1 : ℝ) / 3))
    (hz : z = 270 ^ ((1 : ℝ) / 6)) : z < y ∧ y < x := by
  have hx' : x = (7 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [hx]
    have h1 : Real.sqrt 7 = (7 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      all_goals norm_num
    linarith
  have hy' : y = (17 : ℝ) ^ ((1 : ℝ) / 3) := by
    exact_mod_cast hy
  have hz' : z = (270 : ℝ) ^ ((1 : ℝ) / 6) := by
    exact_mod_cast hz
  have h1 : z < y := by
    rw [hz', hy']
    have h2 : (270 : ℝ) ^ ((1 : ℝ) / 6) < (17 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h4 : (17 : ℝ) ^ ((1 : ℝ) / 3) = ((17 ^ 2) : ℝ) ^ ((1 : ℝ) / 6) := by
        rw [show (17 ^ 2 : ℝ) = (17 : ℝ) ^ (2 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        ring_nf
        norm_num
        all_goals linarith
      rw [h4] at *
      have h5 : (270 : ℝ) < (17 ^ 2 : ℝ) := by norm_num
      have h6 : (270 : ℝ) ^ ((1 : ℝ) / 6) < ((17 ^ 2 : ℝ) : ℝ) ^ ((1 : ℝ) / 6) := by
        apply Real.rpow_lt_rpow
        all_goals linarith
      linarith
    linarith
  have h2 : y < x := by
    rw [hy', hx']
    have h3 : (17 : ℝ) ^ ((1 : ℝ) / 3) < (7 : ℝ) ^ ((1 : ℝ) / 2) := by
      have h4 : (17 : ℝ) ^ ((1 : ℝ) / 3) = ((17 ^ 2) : ℝ) ^ ((1 : ℝ) / 6) := by
        rw [show (17 ^ 2 : ℝ) = (17 : ℝ) ^ (2 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        ring_nf
        norm_num
        all_goals linarith
      have h5 : (7 : ℝ) ^ ((1 : ℝ) / 2) = ((7 ^ 3) : ℝ) ^ ((1 : ℝ) / 6) := by
        rw [show (7 ^ 3 : ℝ) = (7 : ℝ) ^ (3 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        ring_nf
        norm_num
        all_goals linarith
      rw [h4, h5] at *
      have h6 : (17 ^ 2 : ℝ) < (7 ^ 3 : ℝ) := by norm_num
      have h7 : ((17 ^ 2 : ℝ) : ℝ) ^ ((1 : ℝ) / 6) < ((7 ^ 3 : ℝ) : ℝ) ^ ((1 : ℝ) / 6) := by
        apply Real.rpow_lt_rpow
        all_goals linarith
      linarith
    linarith
  constructor
  · exact h1
  · exact h2