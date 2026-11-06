import Mathlib

theorem algebra_141849 : Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * Real.cos (6 * Real.pi / 7) = 1 / 8 := by
  have h1 : Real.cos (6 * Real.pi / 7) = -Real.cos (Real.pi / 7) := by
    have h2 : 6 * Real.pi / 7 = Real.pi - (Real.pi / 7) := by
      ring_nf
    rw [h2]
    rw [Real.cos_pi_sub]

  rw [h1]

  have h2 : Real.sin (8 * (Real.pi / 7)) = 8 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) := by
    have h3 : Real.sin (8 * (Real.pi / 7)) = 2 * Real.sin (4 * (Real.pi / 7)) * Real.cos (4 * (Real.pi / 7)) := by
      rw [show 8 * (Real.pi / 7) = 2 * (4 * (Real.pi / 7)) by ring]
      rw [Real.sin_two_mul]
    have h4 : Real.sin (4 * (Real.pi / 7)) = 2 * Real.sin (2 * (Real.pi / 7)) * Real.cos (2 * (Real.pi / 7)) := by
      rw [show 4 * (Real.pi / 7) = 2 * (2 * (Real.pi / 7)) by ring]
      rw [Real.sin_two_mul]
    have h5 : Real.sin (2 * (Real.pi / 7)) = 2 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) := by
      rw [Real.sin_two_mul]
    rw [h3, h4, h5]
    ring_nf
  -- show $\sin \frac{8\pi}{7} = -\sin \frac{\pi}{7}$
  have h3 : Real.sin (8 * (Real.pi / 7)) = - Real.sin (Real.pi / 7) := by
    have h4 : 8 * (Real.pi / 7) = Real.pi + (Real.pi / 7) := by
      ring_nf
    rw [h4]
    have h5 : Real.sin (Real.pi + (Real.pi / 7)) = - Real.sin (Real.pi / 7) := by
      rw [Real.sin_add, Real.sin_pi, Real.cos_pi]
      ring_nf
    rw [h5]

  have h4 : Real.sin (Real.pi / 7) ≠ 0 := by 
    have h5 : Real.sin (Real.pi / 7) > 0 := by 
      apply Real.sin_pos_of_pos_of_lt_pi 
      linarith [Real.pi_pos] 
      linarith [Real.pi_pos] 
    linarith

  have h6 : Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) = -1 / 8 := by
    have eq1 : Real.sin (8 * (Real.pi / 7)) = - Real.sin (Real.pi / 7) := h3
    rw [h2] at eq1
    have eq3 : Real.sin (Real.pi / 7) * ( -1 - 8 * Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7)) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp eq3) with h7 h8 
    · contradiction 
    · 
      nlinarith

  have eq7 : Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * (-Real.cos (Real.pi / 7)) = 1 / 8 := by
    calc 
      Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * (-Real.cos (Real.pi / 7)) = - (Real.cos (Real.pi / 7) * Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7)) := by
        ring 
      _ = - (-1 / 8) := by 
        rw [h6] 
      _ = 1 / 8 := by
        norm_num
  linarith [eq7]