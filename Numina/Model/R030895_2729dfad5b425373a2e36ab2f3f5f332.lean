import Mathlib

theorem algebra_2913 (a b c d : ℝ) (h₀ : a + b + c + d = 2 * Real.pi) :
    Real.sin a + Real.sin b + Real.sin c + Real.sin d =
    4 * Real.sin ((a + b) / 2) * Real.sin ((b + c) / 2) * Real.sin ((c + a) / 2) := by
  have h₆ : d = 2 * Real.pi - (a + b + c) := by
    linarith
  have h₇ : Real.sin d = - (Real.sin (a + b + c)) := by 
    rw [show d = 2 * Real.pi - (a + b + c) by linarith]
    have h8 : Real.sin (2 * Real.pi - (a + b + c)) = - (Real.sin (a + b + c)) := by 
      rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
      ring
    linarith [h8]

  have h₇' : Real.sin (a + b + c) = 
    Real.sin a * Real.cos b * Real.cos c + Real.cos a * Real.sin b * Real.cos c + Real.cos a * Real.cos b * Real.sin c - Real.sin a * Real.sin b * Real.sin c := by 
    rw [show a + b + c = (a + b) + c by ring]
    rw [Real.sin_add]
    rw [Real.sin_add]
    simp [Real.cos_add]
    ring

  calc 
    Real.sin a + Real.sin b + Real.sin c + Real.sin d 
        = Real.sin a + Real.sin b + Real.sin c - Real.sin (a + b + c) := by 
          rw [h₇]
          <;> ring
    _ = Real.sin a + Real.sin b + Real.sin c - ( 
        Real.sin a * Real.cos b * Real.cos c + Real.cos a * Real.sin b * Real.cos c + Real.cos a * Real.cos b * Real.sin c - Real.sin a * Real.sin b * Real.sin c 
      ) := by 
        rw [h₇']
    _ = 4 * Real.sin ((a + b) / 2) * Real.sin ((b + c) / 2) * Real.sin ((c + a) / 2) := by
      have h10 : Real.sin ((a + b) / 2) = Real.sin ((a / 2) + (b / 2)) := by ring_nf
      have h11 : Real.sin ((b + c) / 2) = Real.sin ((b / 2) + (c / 2)) := by ring_nf
      have h12 : Real.sin ((c + a) / 2) = Real.sin ((c / 2) + (a / 2)) := by ring_nf
      rw [h10, h11, h12]
      have h13 : Real.sin ((a / 2) + (b / 2)) = Real.sin (a / 2) * Real.cos (b / 2) + Real.cos (a / 2) * Real.sin (b / 2) := by 
        rw [Real.sin_add]
      have h14 : Real.sin ((b / 2) + (c / 2)) = Real.sin (b / 2) * Real.cos (c / 2) + Real.cos (b / 2) * Real.sin (c / 2) := by 
        rw [Real.sin_add]
      have h15 : Real.sin ((c / 2) + (a / 2)) = Real.sin (c / 2) * Real.cos (a / 2) + Real.cos (c / 2) * Real.sin (a / 2) := by 
        rw [Real.sin_add]
      rw [h13, h14, h15]
      have h16 : Real.sin a = 2 * Real.sin (a / 2) * Real.cos (a / 2) := by 
        rw [← Real.sin_two_mul]
        ring_nf
      have h17 : Real.sin b = 2 * Real.sin (b / 2) * Real.cos (b / 2) := by 
        rw [← Real.sin_two_mul]
        ring_nf
      have h18 : Real.sin c = 2 * Real.sin (c / 2) * Real.cos (c / 2) := by 
        rw [← Real.sin_two_mul]
        ring_nf
      have h19 : Real.cos a = 2 * Real.cos (a / 2)^2 - 1 := by 
        rw [← Real.cos_two_mul]
        ring_nf
      have h20 : Real.cos b = 2 * Real.cos (b / 2)^2 - 1 := by 
        rw [← Real.cos_two_mul]
        ring_nf
      have h21 : Real.cos c = 2 * Real.cos (c / 2)^2 - 1 := by 
        rw [← Real.cos_two_mul]
        ring_nf
      rw [h16, h17, h18, h19, h20, h21] 
      ring_nf
      <;> 
      simp [Real.sin_sq, Real.cos_sq]
      <;> 
      nlinarith [sq_nonneg (Real.sin (a / 2) - Real.sin (b / 2)), sq_nonneg (Real.sin (b / 2) - Real.sin (c / 2)), sq_nonneg (Real.sin (c / 2) - Real.sin (a / 2)), 
                  sq_nonneg (Real.cos (a / 2) - Real.cos (b / 2)), sq_nonneg (Real.cos (b / 2) - Real.cos (c / 2)), sq_nonneg (Real.cos (c / 2) - Real.cos (a / 2))]