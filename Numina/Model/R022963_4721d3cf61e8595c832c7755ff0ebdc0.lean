import Mathlib

theorem algebra_12976 (cos7 : Real) (hcos7 : cos7 = Real.cos (2 * Real.pi / 7)) (h : cos7 + Real.cos (4 * Real.pi / 7) + Real.cos (6 * Real.pi / 7) = -0.5) :
    (Real.cos (Real.pi / 7))^2 + (Real.cos (2 * Real.pi / 7))^2 + (Real.cos (3 * Real.pi / 7))^2 +
    (Real.cos (4 * Real.pi / 7))^2 + (Real.cos (5 * Real.pi / 7))^2 + (Real.cos (6 * Real.pi / 7))^2 = 2.5 := by

  have h1 : Real.cos (6 * Real.pi / 7) = - Real.cos (Real.pi / 7) := by
    have h1 : 6 * Real.pi / 7 = Real.pi - Real.pi / 7 := by
      ring
    rw [h1]
    rw [Real.cos_pi_sub]

  have h2 : Real.cos (5 * Real.pi / 7) = - Real.cos (2 * Real.pi / 7) := by
    have h2 : 5 * Real.pi / 7 = Real.pi - (2 * Real.pi / 7) := by
      ring
    rw [h2]
    rw [Real.cos_pi_sub]

  have h3 : Real.cos (4 * Real.pi / 7) = - Real.cos (3 * Real.pi / 7) := by
    have h3 : 4 * Real.pi / 7 = Real.pi - (3 * Real.pi / 7) := by
      ring
    rw [h3]
    rw [Real.cos_pi_sub]

  have h4 : (Real.cos (Real.pi / 7))^2 + (Real.cos (2 * Real.pi / 7))^2 + (Real.cos (3 * Real.pi / 7))^2 +
    (Real.cos (4 * Real.pi / 7))^2 + (Real.cos (5 * Real.pi / 7))^2 + (Real.cos (6 * Real.pi / 7))^2 = 2 * (Real.cos (Real.pi / 7) ^ 2 + Real.cos (2 * Real.pi / 7) ^ 2 + Real.cos (3 * Real.pi / 7) ^ 2) := by

    have h5 : Real.cos (4 * Real.pi / 7) = - Real.cos (3 * Real.pi / 7) := h3
    have h6 : Real.cos (5 * Real.pi / 7) = - Real.cos (2 * Real.pi / 7) := h2
    have h7 : Real.cos (6 * Real.pi / 7) = - Real.cos (Real.pi / 7) := h1

    have h8 : Real.cos (4 * Real.pi / 7) ^ 2 = Real.cos (3 * Real.pi / 7) ^ 2 := by
      rw [h5]
      ring

    have h9 : Real.cos (5 * Real.pi / 7) ^ 2 = Real.cos (2 * Real.pi / 7) ^ 2 := by
      rw [h6]
      ring

    have h10 : Real.cos (6 * Real.pi / 7) ^ 2 = Real.cos (Real.pi / 7) ^ 2 := by
      rw [h7]
      ring

    linarith [h8, h9, h10]

  have h5 : Real.cos (Real.pi / 7) ^ 2 + Real.cos (2 * Real.pi / 7) ^ 2 + Real.cos (3 * Real.pi / 7) ^ 2 = 5 / 4 := by
    have h1 : Real.cos (6 * Real.pi / 7) = - Real.cos (Real.pi / 7) := h1
    have h1' : cos7 + Real.cos (4 * Real.pi / 7) + Real.cos (6 * Real.pi / 7) = -0.5 := h
    have h3' : Real.cos (4 * Real.pi / 7) = - Real.cos (3 * Real.pi / 7) := h3
    rw [hcos7] at h1'

    have h7 : Real.cos (2 * Real.pi / 7) - Real.cos (3 * Real.pi / 7) - Real.cos (Real.pi / 7) = -0.5 := by
      rw [h3', h1] at h1'
      ring_nf at h1'
      linarith

    have h7' : Real.cos (Real.pi / 7) ^ 2 = (1 + Real.cos (2 * Real.pi / 7)) / 2 := by
      have h7 : Real.cos (2 * Real.pi / 7) = 2 * Real.cos (Real.pi / 7) ^ 2 - 1 := by
        have h8 : 2 * Real.pi / 7 = 2 * (Real.pi / 7) := by
          ring
        rw [h8]
        rw [Real.cos_two_mul]
      linarith [h7]

    have h8' : Real.cos (2 * Real.pi / 7) ^ 2 = (1 + Real.cos (4 * Real.pi / 7)) / 2 := by
      have h8 : Real.cos (4 * Real.pi / 7) = 2 * Real.cos (2 * Real.pi / 7) ^ 2 - 1 := by
        have h9 : 4 * Real.pi / 7 = 2 * (2 * Real.pi / 7) := by
          ring
        rw [h9]
        rw [Real.cos_two_mul]
      linarith [h8]

    have h9' : Real.cos (3 * Real.pi / 7) ^ 2 = (1 + Real.cos (6 * Real.pi / 7)) / 2 := by
      have h9 : Real.cos (6 * Real.pi / 7) = 2 * Real.cos (3 * Real.pi / 7) ^ 2 - 1 := by
        have h10 : 6 * Real.pi / 7 = 2 * (3 * Real.pi / 7) := by
          ring
        rw [h10]
        rw [Real.cos_two_mul]
      linarith [h9]

    have h10' : Real.cos (6 * Real.pi / 7) = - Real.cos (Real.pi / 7) := h1

    norm_num at h7

    nlinarith [h7', h8', h9', h10', h7, Real.cos_sq_add_sin_sq (2 * Real.pi / 7), Real.cos_sq_add_sin_sq (Real.pi / 7), Real.cos_sq_add_sin_sq (3 * Real.pi / 7)]

  calc
    (Real.cos (Real.pi / 7))^2 + (Real.cos (2 * Real.pi / 7))^2 + (Real.cos (3 * Real.pi / 7))^2 +
      (Real.cos (4 * Real.pi / 7))^2 + (Real.cos (5 * Real.pi / 7))^2 + (Real.cos (6 * Real.pi / 7))^2 = 2 * (Real.cos (Real.pi / 7) ^ 2 + Real.cos (2 * Real.pi / 7) ^ 2 + Real.cos (3 * Real.pi / 7) ^ 2) := by
        linarith [h4]
    _ = 2 * (5 / 4) := by
      rw [h5]
    _ = 2.5 := by
      norm_num