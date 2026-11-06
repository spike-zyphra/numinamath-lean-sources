import Mathlib

open Real

theorem calculus_136467 (f : ℝ → ℝ) (hf : f = fun x => (x^3 + 7 * x) ^ ((1 : ℝ) / 3)) (x : ℝ) (hx : x = 1.012) :
    deriv f 1 * (x - 1) + f 1 = 2.01 := by

  have h2 : f 1 = (2 : ℝ) := by
    rw [hf]
    have h3 : (1 : ℝ) ^ 3 + 7 * (1 : ℝ) = (8 : ℝ) := by norm_num
    simp [h3]
    have h4 : (8 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
      have h5 : (8 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
        have h1 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
        rw [h1]
        have h2 : ((2 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals linarith [show (0 : ℝ) < (2 : ℝ) by norm_num]
        linarith
      linarith
    linarith [h4]

  have h3 : deriv f 1 = (5 / 6 : ℝ) := by
    rw [hf]
    simp [deriv_pow, deriv_add, deriv_pow, mul_comm]
    have h11 : ((8 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
      have h2 : (8 : ℝ) = 2 ^ (3 : ℝ) := by norm_num
      rw [h2]
      have h3 : ((2 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals
          norm_num
      linarith
    have h12 : ((8 : ℝ) : ℝ) ^ ((-2 : ℝ) / 3) = (1 / 4 : ℝ) := by
      have h3 : (8 : ℝ) ^ ((-2 : ℝ) / 3) = ((2 : ℝ) ^ (3 : ℝ)) ^ ((-2 : ℝ) / 3) := by
        norm_num
      rw [h3]
      have h4 : ((2 : ℝ) ^ (3 : ℝ)) ^ ((-2 : ℝ) / 3) = (2 : ℝ) ^ (-2 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals
          norm_num
      rw [h4]
      norm_num
    norm_num [h11, h12]
    all_goals linarith

  have hx2 : x - 1 = (0.012 : ℝ) := by
    rw [hx]
    all_goals norm_num

  rw [h3, hx2, h2]
  all_goals norm_num