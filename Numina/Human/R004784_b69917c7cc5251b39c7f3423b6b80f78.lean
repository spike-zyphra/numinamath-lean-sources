import Mathlib

open Real

theorem algebra_323320 : sin (130 * π / 180) ^ 2 + sin (70 * π / 180) * cos (80 * π / 180) = 3 / 4 := by
  have h1 : sin (130 * π / 180) = sin (50 * π / 180) := by
    have h1 : 130 * π / 180 = π - 50 * π / 180 := by ring
    rw [h1]
    rw [sin_pi_sub]
  rw [h1]
  have h2 : sin (50 * π / 180) ^ 2 + sin (70 * π / 180) * cos (80 * π / 180) = 3 / 4 := by
    have h3 : sin (50 * π / 180) ^ 2 = (1 - cos (100 * π / 180)) / 2 := by
      have h : sin (50 * π / 180) ^ 2 + cos (50 * π / 180) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (50 * π / 180)
      have h4 : cos (100 * π / 180) = 2 * cos (50 * π / 180) ^ 2 - 1 := by
        have h5 : 100 * π / 180 = 2 * (50 * π / 180) := by ring
        rw [h5]
        rw [cos_two_mul]
      nlinarith [h, h4]
    have h4 : sin (70 * π / 180) * cos (80 * π / 180) = (1 / 2) * (sin (150 * π / 180) + sin (70 * π / 180 - 80 * π / 180)) := by
      have h : sin (70 * π / 180) * cos (80 * π / 180) = (1 / 2) * (sin (70 * π / 180 + 80 * π / 180) + sin (70 * π / 180 - 80 * π / 180)) := by
        rw [sin_add, sin_sub]
        ring
      rw [h]
      have h5 : 70 * π / 180 + 80 * π / 180 = 150 * π / 180 := by ring
      rw [h5]
    have h5 : sin (150 * π / 180) = 1 / 2 := by
      have h6 : 150 * π / 180 = π - π / 6 := by ring
      rw [h6]
      rw [sin_pi_sub]
      have h7 : sin (π / 6) = 1 / 2 := by
        exact sin_pi_div_six
      rw [h7]
    have h6 : sin (70 * π / 180 - 80 * π / 180) = - sin (10 * π / 180) := by
      have h7 : 70 * π / 180 - 80 * π / 180 = -(10 * π / 180) := by ring
      rw [h7]
      rw [sin_neg]
    rw [h5] at h4
    rw [h6] at h4
    have h7 : sin (50 * π / 180) ^ 2 + sin (70 * π / 180) * cos (80 * π / 180) = (1 - cos (100 * π / 180)) / 2 + (1 / 2) * (1 / 2 + (- sin (10 * π / 180))) := by
      linarith [h3, h4]
    have h8 : (1 - cos (100 * π / 180)) / 2 + (1 / 2) * (1 / 2 + (- sin (10 * π / 180))) = 3 / 4 := by
      have h9 : cos (100 * π / 180) + sin (10 * π / 180) = 0 := by
        have h10 : 100 * π / 180 = π - 80 * π / 180 := by ring
        rw [h10]
        rw [cos_pi_sub]
        have h11 : cos (80 * π / 180) = sin (10 * π / 180) := by
          have h12 : 80 * π / 180 = π / 2 - 10 * π / 180 := by ring
          rw [h12]
          rw [cos_pi_div_two_sub]
        linarith [h11]
      nlinarith [h9]
    linarith [h7, h8]
  linarith [h2]