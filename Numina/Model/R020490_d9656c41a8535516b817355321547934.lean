import Mathlib

theorem algebra_163447 (X : ℝ) (hX : X = 2 * Real.sin (2 * Real.pi / 9) ∨ X = 2 * Real.sin (8 * Real.pi / 9) ∨ X = 2 * Real.sin (14 * Real.pi / 9)) :
    X^3 - 3 * X + Real.sqrt 3 = 0 := by 
  rcases hX with (hX | hX | hX)
  · -- Case where $X = 2 \sin \frac{2 \pi}{9}$
    have h1 : X = 2 * Real.sin (2 * Real.pi / 9) := hX
    have h2 : Real.sin (3 * (2 * Real.pi / 9)) = 3 * Real.sin (2 * Real.pi / 9) - 4 * Real.sin (2 * Real.pi / 9) ^ 3 := by
      rw [Real.sin_three_mul]
    -- Compute $\sin(3 \cdot \frac{2\pi}{9}) = \sin(\frac{2\pi}{3}) = \frac{\sqrt{3}}{2}$
    have h3 : Real.sin (3 * (2 * Real.pi / 9)) = Real.sqrt 3 / 2 := by
      have h4 : 3 * (2 * Real.pi / 9) = Real.pi - Real.pi / 3 := by 
        linarith [Real.pi_pos]
      rw [h4]
      have h5 : Real.sin (Real.pi - Real.pi / 3) = Real.sin (Real.pi / 3) := by
        rw [Real.sin_pi_sub]
      rw [h5]
      have h6 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      rw [h6]
    -- Substitute h2 into h3
    rw [h2] at h3
    -- Let $X = 2 \sin \theta$, so $\sin \theta = \frac{X}{2}$
    have h7 : Real.sin (2 * Real.pi / 9) = X / 2 := by 
      rw [h1]
      ring_nf
    -- Substitute into the equation and simplify
    rw [h7] at h3
    -- Simplify the equation $\frac{\sqrt{3}}{2} = 3 \cdot \frac{X}{2} - 4 \cdot \left( \frac{X}{2} \right)^3$
    nlinarith [Real.sqrt_pos.mpr (by linarith [Real.pi_pos] : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
  · -- Case where $X = 2 \sin \frac{8 \pi}{9}$
    have h1 : X = 2 * Real.sin (8 * Real.pi / 9) := hX
    have h2 : Real.sin (3 * (8 * Real.pi / 9)) = 3 * Real.sin (8 * Real.pi / 9) - 4 * Real.sin (8 * Real.pi / 9) ^ 3 := by
      rw [Real.sin_three_mul]
    -- Compute $\sin(3 \cdot \frac{8\pi}{9}) = \sin\left(\frac{8\pi}{3}\right) = \sin\left(2\pi + \frac{2\pi}{3}\right) = \sin\left(\frac{2\pi}{3}\right) = \frac{\sqrt{3}}{2}$
    have h3 : Real.sin (3 * (8 * Real.pi / 9)) = Real.sqrt 3 / 2 := by
      have h4 : 3 * (8 * Real.pi / 9) = 2 * Real.pi + (2 * Real.pi / 3) := by
        linarith [Real.pi_pos]
      rw [h4]
      have h5 : Real.sin (2 * Real.pi + (2 * Real.pi / 3)) = Real.sin (2 * Real.pi / 3) := by 
        rw [Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]
        norm_num
      rw [h5]
      have h6 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
        have h7 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by 
          linarith [Real.pi_pos]
        rw [h7]
        have h8 : Real.sin (Real.pi - Real.pi / 3) = Real.sin (Real.pi / 3) := by
          rw [Real.sin_pi_sub]
        rw [h8]
        have h9 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
        rw [h9]
      rw [h6]
    -- Substitute h2 into h3
    rw [h2] at h3
    -- Let $X = 2 \sin \theta$, so $\sin \theta = \frac{X}{2}$
    have h7 : Real.sin (8 * Real.pi / 9) = X / 2 := by 
      rw [h1]
      ring_nf
    -- Substitute into the equation and simplify
    rw [h7] at h3
    -- Simplify the equation $\frac{\sqrt{3}}{2} = 3 \cdot \frac{X}{2} - 4 \cdot \left( \frac{X}{2} \right)^3$
    nlinarith [Real.sqrt_pos.mpr (by linarith [Real.pi_pos] : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
  · -- Case where $X = 2 \sin \frac{14 \pi}{9}$
    have h1 : X = 2 * Real.sin (14 * Real.pi / 9) := hX
    have h2 : Real.sin (3 * (14 * Real.pi / 9)) = 3 * Real.sin (14 * Real.pi / 9) - 4 * Real.sin (14 * Real.pi / 9) ^ 3 := by
      rw [Real.sin_three_mul]
    -- Compute $\sin(3 \cdot \frac{14\pi}{9}) = \sin\left(\frac{14\pi}{3}\right) = \sin\left(4\pi + \frac{2\pi}{3}\right) = \sin\left(\frac{2\pi}{3}\right) = \frac{\sqrt{3}}{2}$
    have h3 : Real.sin (3 * (14 * Real.pi / 9)) = Real.sqrt 3 / 2 := by
      have h4 : 3 * (14 * Real.pi / 9) = 4 * Real.pi + (2 * Real.pi / 3) := by
        linarith [Real.pi_pos]
      rw [h4]
      have h5 : Real.sin (4 * Real.pi + (2 * Real.pi / 3)) = Real.sin (2 * Real.pi / 3) := by
        have : 4 * Real.pi + (2 * Real.pi / 3) = 2 * Real.pi + (2 * Real.pi + (2 * Real.pi / 3)) := by ring
        rw [this]
        have h8 : Real.sin (2 * Real.pi + (2 * Real.pi + (2 * Real.pi / 3))) = Real.sin (2 * Real.pi + (2 * Real.pi / 3)) := by 
          rw [Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]
          norm_num
        rw [h8]
        have h9 : Real.sin (2 * Real.pi + (2 * Real.pi / 3)) = Real.sin (2 * Real.pi / 3) := by 
          rw [Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]
          norm_num
        rw [h9]
      rw [h5]
      have h6 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
        have h7 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by 
          linarith [Real.pi_pos]
        rw [h7]
        have h8 : Real.sin (Real.pi - Real.pi / 3) = Real.sin (Real.pi / 3) := by
          rw [Real.sin_pi_sub]
        rw [h8]
        have h9 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
        rw [h9]
      rw [h6]
    -- Substitute h2 into h3
    rw [h2] at h3
    -- Let $X = 2 \sin \theta$, so $\sin \theta = \frac{X}{2}$
    have h7 : Real.sin (14 * Real.pi / 9) = X / 2 := by 
      rw [h1]
      ring_nf
    -- Substitute into the equation and simplify
    rw [h7] at h3
    -- Simplify the equation $\frac{\sqrt{3}}{2} = 3 \cdot \frac{X}{2} - 4 \cdot \left( \frac{X}{2} \right)^3$
    nlinarith [Real.sqrt_pos.mpr (by linarith [Real.pi_pos] : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]