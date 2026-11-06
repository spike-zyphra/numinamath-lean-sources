import Mathlib

open Real Set
open scoped Real

/- Find $\sin 20^\circ \sin 40^\circ \sin 60^\circ \sin 80^\circ \sin 100^\circ \sin 120^\circ \sin 140^\circ \sin 160^\circ.$ -/
theorem calculus_22456 : sin (π / 9) * sin (2 * π / 9) * sin (3 * π / 9) * sin (4 * π / 9) * sin (5 * π / 9) * sin (6 * π / 9) * sin (7 * π / 9) * sin (8 * π / 9) = 9 / 256 := by
  -- sin 3π/9 = sin 6π/9 = sin π/3 = √3/2
  have h1: 3*π/9 = π/3 := by ring
  have h2: 6*π/9 = π - π/3 := by ring
  rw [h1,h2, sin_pi_sub, sin_pi_div_three]
  -- notice that sin 8π/9 = sin π/9, sin 7π/9 = sin 2π/9
  have h3: 8*π/9 = π-π/9 := by ring
  have h4: 7*π/9 = π - 2*π/9 := by ring
  rw [h3, h4, sin_pi_sub, sin_pi_sub]
  -- and sin 4π/9 = sin 5π/9 = cos π/18
  have h5: 4*π/9 = π/2 - π/18 := by ring
  have h6: 5*π/9 = π - 4*π/9 := by ring
  rw [h6, h5, sin_pi_sub, sin_pi_div_two_sub]
  -- group same term together
  have h7: sin (π / 9) * sin (2 * π / 9) * (√3 / 2) * cos (π / 18) * cos (π / 18) * (√3 / 2) * sin (2 * π / 9) * sin (π / 9) = 
    (cos (π/18) * sin (π/9) * sin (2*π/9) * (√3/2))^2 := by ring
  rw [h7]
  -- by product-to-sum, sin π/9 *  sin 2π/9 = (cos π/9 - cos π/3)/2
  have pro_to_sum1(a b:ℝ): sin a * sin b = (cos (b-a) - cos (a+b))/2 := by
    rw [cos_sub, cos_add]; ring
  have h8: sin (π/9) * sin (2*π/9) = (cos (π/9) - 1/2)/2 := by
    rw [pro_to_sum1 (π/9) (2*π/9)]
    have hh1: 2*π/9 - π/9 = π/9 := by ring
    have hh2: π/9 + 2*π/9 = π/3 := by ring
    rw [hh1, hh2, cos_pi_div_three]
  -- by product-to-sum again, notice that cos π/18 cos π/9 = (cos π/18 + cos π/6)/2
  have pro_to_sum2(a b:ℝ): cos a * cos b = (cos (b-a) + cos (b+a))/2 := by
    rw [cos_sub, cos_add]; ring
  -- simplify, the following holds.
  have h9: cos (π/18) * sin (π/9) * sin (2*π/9) = √3/8 := by
    rw [mul_assoc (cos (π/18)), h8]
    have: cos (π / 18) * ((cos (π / 9) - 1 / 2) / 2) = 
      (cos (π/18) * cos (π/9))/2 - cos (π/18) /4 := by ring
    rw [this, pro_to_sum2 (π/18) (π/9)]
    have hh1: π/9 - π/18 = π/18 := by ring
    have hh2: π/9 + π/18 = π/6 := by ring
    rw [hh1, hh2, cos_pi_div_six]; ring
  rw [h9]
  -- so it simplifies to (√3/8 * √3/2)^2 = (3/16)^2 = 9/256
  field_simp; ring