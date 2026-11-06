import Mathlib

open Real

theorem algebra_130544 : sin (75 * π / 180) ^ 8 - cos (75 * π / 180) ^ 8 = 7 * sqrt 3 / 16 := by
  have h1 : sin (75 * π / 180) = sin (5 * π / 12) := by 
    ring_nf
  have h2 : cos (75 * π / 180) = cos (5 * π / 12) := by 
    ring_nf
  rw [h1, h2]
  -- Now we compute $\sin^8(5\pi/12) - \cos^8(5\pi/12)$
  have h3 : sin (5 * π / 12) ^ 8 - cos (5 * π / 12) ^ 8 = (sin (5 * π / 12) ^ 4 - cos (5 * π / 12) ^ 4) * (sin (5 * π / 12) ^ 4 + cos (5 * π / 12) ^ 4) := by
    ring
  -- Factor $\sin^4 \theta - \cos^4 \theta$
  have h4 : sin (5 * π / 12) ^ 4 - cos (5 * π / 12) ^ 4 = (sin (5 * π / 12) ^ 2 - cos (5 * π / 12) ^ 2) * (sin (5 * π / 12) ^ 2 + cos (5 * π / 12) ^ 2) := by 
    ring
  -- $\sin^2 \theta + \cos^2 \theta = 1$
  have h5 : sin (5 * π / 12) ^ 2 + cos (5 * π / 12) ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq (5 * π / 12)
  -- $\sin^2 \theta - \cos^2 \theta = -\cos(2\theta)$
  have h6 : sin (5 * π / 12) ^ 2 - cos (5 * π / 12) ^ 2 = -cos (2 * (5 * π / 12)) := by
    have h7 : cos (2 * (5 * π / 12)) = 2 * cos (5 * π / 12) ^ 2 - 1 := by 
      rw [cos_two_mul]
    have h8 : sin (5 * π / 12) ^ 2 + cos (5 * π / 12) ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq (5 * π / 12)
    nlinarith [h7, h8]
  -- So $\sin^4 \theta - \cos^4 \theta = -\cos(2\theta)$
  have h9 : sin (5 * π / 12) ^ 4 - cos (5 * π / 12) ^ 4 = (-cos (2 * (5 * π / 12)) ) * (1) := by 
    rw [h4, h6, h5]
    <;> ring
  -- Compute $\sin^4 \theta + \cos^4 \theta$
  have h10 : sin (5 * π / 12) ^ 4 + cos (5 * π / 12) ^ 4 = 1 - (1 / 2) * (sin (2 * (5 * π / 12)) ) ^ 2 := by 
    have h12 : sin (2 * (5 * π / 12)) = 2 * sin (5 * π / 12) * cos (5 * π / 12) := by 
      rw [sin_two_mul]
    have h13 : sin (5 * π / 12) ^ 4 + cos (5 * π / 12) ^ 4 = (sin (5 * π / 12) ^ 2 + cos (5 * π / 12) ^ 2) ^ 2 - 2 * (sin (5 * π / 12) * cos (5 * π / 12)) ^ 2 := by 
      ring
    have h14 : sin (5 * π / 12) ^ 2 + cos (5 * π / 12) ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq (5 * π / 12)
    have h15 : (sin (5 * π / 12) * cos (5 * π / 12)) ^ 2 = (1 / 4) * (sin (2 * (5 * π / 12)) ) ^ 2 := by 
      calc 
        (sin (5 * π / 12) * cos (5 * π / 12)) ^ 2 = ( (1 / 2) * (2 * sin (5 * π / 12) * cos (5 * π / 12)) ) ^ 2 := by ring
        _ = ( (1 / 2) * sin (2 * (5 * π / 12)) ) ^ 2 := by rw [h12]
        _ = (1 / 4) * (sin (2 * (5 * π / 12)) ) ^ 2 := by ring
    rw [h13, h14, h15]
    <;> ring
  -- Now we rewrite h3 with h9 and h10
  rw [h3, h9, h10]
  -- Compute $\cos(5\pi/6)$ and $\sin(5\pi/6)$
  have h11 : cos (2 * (5 * π / 12)) = -sqrt 3 / 2 := by 
    have h16 : 2 * (5 * π / 12) = π - (π / 6) := by 
      linarith [Real.pi_pos]
    rw [h16]
    rw [cos_pi_sub]
    have h17 : cos (π / 6) = sqrt 3 / 2 := by 
      exact cos_pi_div_six
    rw [h17]
    all_goals ring
  -- $\sin(5\pi/6) = 1/2$
  have h18 : sin (2 * (5 * π / 12)) = 1 / 2 := by
    have h19 : 2 * (5 * π / 12) = π - (π / 6) := by
      linarith [Real.pi_pos]
    rw [h19]
    rw [sin_pi_sub]
    have h20 : sin (π / 6) = 1 / 2 := by 
      exact sin_pi_div_six
    rw [h20]
  -- Substitute h11 and h18 into the expression
  rw [h11, h18]
  -- Final computation
  ring_nf
  <;> field_simp
  <;> ring