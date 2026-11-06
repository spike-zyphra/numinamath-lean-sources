import Mathlib
open Real

-- This theorem is not in mathlib4, but is the fundamental triangle inequality for real number. Whats more, the cos_add_cos is in mathlib4, thus I put it here as a theorem.
theorem sin_add_sin {x y : ℝ} : sin x + sin y = 2 * sin ((x+y)/2) * cos ((x-y)/2) := by
    let u:ℝ := (x+y)/2
    let v:ℝ := (x-y)/2
    rw [show x = u+v by ring_nf, show y = u-v by ring_nf]
    simp
    rw [sin_add, sin_sub]; linarith

/-
Express $\frac{\sin 10+\sin 20+\sin 30+\sin 40+\sin 50+\sin 60+\sin 70+\sin 80}{\cos 5 \cos 10 \cos 20}$ without using trigonometric functions.
-/
theorem algebra_610957 : ( sin (10 * π / 180) +  sin (20 * π / 180) +  sin (30 * π / 180) +  sin (40 * π / 180) +  sin (50 * π / 180) +  sin (60 * π / 180) +  sin (70 * π / 180) +  sin (80 * π / 180))/( cos (5 * π / 180) *  cos (10 * π / 180) *  cos (20 * π / 180)) = 4 * sqrt 2 := by

  -- The sum of cos to mul of cos
  have sum_sin:  sin (10 * π / 180) +  sin (20 * π / 180) +  sin (30 * π / 180) +  sin (40 * π / 180) +  sin (50 * π / 180) +  sin (60 * π / 180) +  sin (70 * π / 180) +  sin (80 * π / 180) = (sin (10 * π / 180) + sin (80 * π / 180)) + (sin (20 * π / 180) + sin (70 * π / 180)) + (sin (30 * π / 180) + sin (60 * π / 180)) + (sin (40 * π / 180) + sin (50 * π / 180)) := by ring_nf
  

  -- Use the cos_add_cos and sin_add_sin recursively to simplify the equation
  have h0: (sin (10 * π / 180) + sin (80 * π / 180)) + (sin (20 * π / 180) + sin (70 * π / 180)) + (sin (30 * π / 180) + sin (60 * π / 180)) + (sin (40 * π / 180) + sin (50 * π / 180)) = 4*sqrt 2 *  (cos (20 * π / 180)) * (cos (10 * π / 180)) * (cos (5 * π / 180)):= by
    calc
      -- rearrange the terms so that we can use the sin_add_sin
      _ = 2*(sin (45 * π / 180))*(cos (-35 * π / 180)) + 2*(sin (45 * π / 180))*(cos (-25 * π / 180)) + 2*(sin (45 * π / 180))*(cos (-15 * π / 180)) + 2*(sin (45 * π / 180))*(cos (-5 * π / 180)) := by
        rw [sin_add_sin, sin_add_sin, sin_add_sin, sin_add_sin]
        ring_nf
      -- rearrange the terms again
      _ = 2*(sin (45 * π / 180))*(cos (-35 * π / 180)+cos (-25 * π / 180)+cos (-15 * π / 180)+cos (-5 * π / 180)) := by ring_nf
      _ = 2*(sin (π / 4))*((cos (-5 * π / 180)+cos (-35 * π / 180)) + (cos (-15 * π / 180)+cos (-25 * π / 180))) := by ring_nf
      -- use cos_add_cos
      _ = 2*(sin (π / 4))*(2 * (cos (-20 * π / 180)) * (cos (15 * π / 180)) + 2 * (cos (-20 * π / 180)) * (cos (5 * π / 180))) := by
        rw [cos_add_cos, cos_add_cos]; ring_nf
      -- rerarrange the terms
      _ = 4 * (sin (π / 4)) * (cos (-20 * π / 180)) * ((cos (15 * π / 180)) + (cos (5 * π / 180))) := by ring_nf
      -- use cos_add_cos again
      _ = 4 * (sin (π / 4))  * (cos (-20 * π / 180)) * (2 * (cos (10 * π / 180)) * (cos (5 * π / 180))) := by
        rw [cos_add_cos]; ring_nf
      _ = 8 * (sin (π / 4)) * (cos (-(20 * π / 180))) * (cos (10 * π / 180)) * (cos (5 * π / 180)) := by ring_nf
      -- cos -x = cos x
      _ = 8 * (sin (π / 4)) * (cos (20 * π / 180)) * (cos (10 * π / 180)) * (cos (5 * π / 180)) := by rw [cos_neg]
      -- rw the sin pi/4 = sqrt 2 / 2
      _ = 4*sqrt 2 *  (cos (20 * π / 180)) * (cos (10 * π / 180)) * (cos (5 * π / 180)) := by rw[sin_pi_div_four]; ring_nf

  rw [h0] at sum_sin

  rw [sum_sin]
  
  -- cos (20 * π / 180) > 0, thus we can cancel this term
  have deno_nonzero1: cos (20 * π / 180) > 0 := by
    apply cos_pos_of_le_one
    have _1: 20 * π / 180 > 0 := by field_simp
    rw [abs_of_pos]
    have : π ≤ 4 := by exact pi_le_four
    linarith; linarith
  
  -- cos (10 * π / 180) > 0, thus we can cancel this term
  have deno_nonzero2: cos (10 * π / 180) > 0 := by
    apply cos_pos_of_le_one
    have _1: 10 * π / 180 > 0 := by field_simp
    rw [abs_of_pos]
    have : π ≤ 4 := by exact pi_le_four
    linarith; linarith
  
  -- cos (5 * π / 180) > 0, thus we can cancel this term
  have deno_nonzero3: cos (5 * π / 180) > 0 := by
    apply cos_pos_of_le_one
    have _1: 5 * π / 180 > 0 := by field_simp
    rw [abs_of_pos]
    have : π ≤ 4 := by exact pi_le_four
    linarith; linarith
  
  field_simp; ring_nf

        



      
