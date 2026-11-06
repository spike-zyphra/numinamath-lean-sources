import Mathlib

theorem algebra_7714 : Real.tan (329 * Real.pi / 180) = -Real.tan (31 * Real.pi / 180) ∧
    Real.sin (167 * Real.pi / 180) = Real.sin (13 * Real.pi / 180) := by
  have htan : Real.tan (329 * Real.pi / 180) = -Real.tan (31 * Real.pi / 180) := by
    have htan1 : Real.tan (329 * Real.pi / 180) = Real.tan (2 * Real.pi - (31 * Real.pi / 180)) := by
      ring_nf
    rw [htan1]
    have htan2 : Real.tan (2 * Real.pi - (31 * Real.pi / 180)) = Real.tan (Real.pi - (31 * Real.pi / 180)) := by
      have h1 : 2 * Real.pi - (31 * Real.pi / 180) = Real.pi - (31 * Real.pi / 180) + Real.pi := by
        linarith [Real.pi_pos]
      rw [h1]
      rw [Real.tan_add_pi]
    rw [htan2]
    have htan3 : Real.tan (Real.pi - (31 * Real.pi / 180)) = -Real.tan (31 * Real.pi / 180) := by
      rw [Real.tan_pi_sub]
    rw [htan3]
  have hsin : Real.sin (167 * Real.pi / 180) = Real.sin (13 * Real.pi / 180) := by
    have h1 : 167 * Real.pi / 180 = Real.pi - (13 * Real.pi / 180) := by
      linarith [Real.pi_pos]
    rw [h1]
    have h2 : Real.sin (Real.pi - (13 * Real.pi / 180)) = Real.sin (13 * Real.pi / 180) := by
      rw [Real.sin_pi_sub]
    rw [h2]
  constructor
  · exact htan
  · exact hsin