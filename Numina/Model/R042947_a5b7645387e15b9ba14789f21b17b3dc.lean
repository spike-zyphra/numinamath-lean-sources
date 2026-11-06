import Mathlib

open Real Set
open scoped Real

theorem algebra_203691 : sin (π / 18) * sin (π / 6) * sin (5 * π / 18) * sin (7 * π / 18) = 1 / 16 := by
  have h1 : sin (π / 6) = 1 / 2 := by 
    exact sin_pi_div_six
  have h2 : sin (π / 18) * sin (5 * π / 18) * sin (7 * π / 18) = 1 / 8 := by 
    have h3 : 5 * π / 18 = π / 3 - π / 18 := by 
      linarith [show π / 3 = 6 * π / 18 by linarith [Real.pi_pos]]
    have h4 : 7 * π / 18 = π / 3 + π / 18 := by 
      linarith [show π / 3 = 6 * π / 18 by linarith [Real.pi_pos]]
    rw [h3, h4]
    have h5 : sin (π / 18) * sin (π / 3 - π / 18) * sin (π / 3 + π / 18) = 1 / 8 := by 
      have h6 : sin (π / 3 - π / 18) = sin (π / 3) * cos (π / 18) - cos (π / 3) * sin (π / 18) := by 
        rw [sin_sub]
      have h7 : sin (π / 3 + π / 18) = sin (π / 3) * cos (π / 18) + cos (π / 3) * sin (π / 18) := by 
        rw [sin_add]
      have h8 : sin (π / 3) = Real.sqrt 3 / 2 := by 
        exact sin_pi_div_three
      have h9 : cos (π / 3) = 1 / 2 := by 
        exact cos_pi_div_three
      have h10 : sin (3 * (π / 18) ) = 1 / 2 := by
        have h11 : 3 * (π / 18) = π / 6 := by 
          linarith [Real.pi_pos]
        rw [h11]
        linarith [show sin (π / 6) = 1 / 2 by 
          linarith [Real.sin_pi_div_six]
        ]
      have h11 : sin (3 * (π / 18) ) = 3 * sin (π / 18) - 4 * sin (π / 18) ^ 3 := by 
        rw [show 3 * (π / 18) = 3 * (π / 18) by rfl]
        rw [sin_three_mul]
      have eq1 : 3 * sin (π / 18) - 4 * sin (π / 18) ^ 3 = 1 / 2 := by 
        linarith [h11, h10]
      rw [h6, h7, h8, h9]
      have hcos18 : cos (π / 18) ^ 2 = 1 - sin (π / 18) ^ 2 := by 
        have h15 : cos (π / 18) ^ 2 + sin (π / 18) ^ 2 = 1 := by
          exact cos_sq_add_sin_sq (π / 18)
        linarith
      have eq2 : sin (π / 18) * ((Real.sqrt 3 / 2) * cos (π / 18) - (1 / 2) * sin (π / 18)) * ((Real.sqrt 3 / 2) * cos (π / 18) + (1 / 2) * sin (π / 18)) =
          sin (π / 18) * ((3 / 4) * (cos (π / 18) ) ^ 2 - (1 / 4) * (sin (π / 18) ) ^ 2) := by 
        ring_nf
        <;> simp [Real.sqrt_sq]
        <;> ring
      have eq3 : sin (π / 18) * ((3 / 4) * (cos (π / 18) ) ^ 2 - (1 / 4) * (sin (π / 18) ) ^ 2) = 1 / 8 := by
        have eq6 : sin (π / 18) * ((3 / 4) * (cos (π / 18) ) ^ 2 - (1 / 4) * (sin (π / 18) ) ^ 2) = 
            (1 / 4) * (3 * sin (π / 18) - 4 * sin (π / 18) ^ 3) := by
          have hcos18' : cos (π / 18) ^ 2 = 1 - sin (π / 18) ^ 2 := hcos18
          rw [hcos18']
          nlinarith [sq_nonneg (sin (π / 18) ), sq_nonneg (cos (π / 18) - 1 / 2), sq_nonneg (sin (π / 18) ^ 2 - 1 / 4) ]
        rw [eq6]
        linarith [eq1]
      linarith [eq2, eq3]
    linarith
  calc 
    sin (π / 18) * sin (π / 6) * sin (5 * π / 18) * sin (7 * π / 18)
        = sin (π / 18) * sin (5 * π / 18) * sin (7 * π / 18) * sin (π / 6) := by ring
    _ = (1 / 8) * sin (π / 6) := by
      rw [show sin (π / 18) * sin (5 * π / 18) * sin (7 * π / 18) = 1 / 8 by linarith [h2] ]
      <;> ring
    _ = (1 / 8) * (1 / 2) := by 
      rw [h1]
    _ = 1 / 16 := by 
      norm_num