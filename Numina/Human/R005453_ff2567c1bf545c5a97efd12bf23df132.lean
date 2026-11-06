import Mathlib
open Real
/- Evaluate

$$
\sin \left(1998^{\circ}+237^{\circ}\right) \sin \left(1998^{\circ}-1653^{\circ}\right)
$$ -/
theorem algebra_608369 : sin (1998 * π / 180 + 237 * π / 180) * sin (1998 * π / 180 - 1653 * π / 180) = -1 / 4:= by
  -- Simplify the algebraic expressions
  ring_nf
  -- Prove that sin(149π/12) = sin(5π/12) using periodic property of sine
  have h1 : sin (π * (149 / 12)) = sin (π * (5 / 12)):= by
    apply Real.sin_eq_sin_iff.2
    use -6
    ring_nf
    simp
  -- Prove that sin(23π/12) = sin(-π/12) using periodic property of sine
  have h2 : sin (π * (23 / 12)) = sin (π * (-1 / 12)):= by
    apply Real.sin_eq_sin_iff.2
    use -1
    ring_nf
    simp
  rw [h1, h2]
  -- Use the relationship between sine and cosine: sin(x) = cos(π/2 - x)
  have h3 : sin (π * (5 / 12)) = cos (π / 2 - π * (5 / 12)):= by exact Eq.symm (cos_pi_div_two_sub (π * (5 / 12)))
  rw [h3]
  -- Simplify π * (-1/12) to -π/12
  rw [show π * (-1 / 12) = -(π / 12) by ring_nf]
  -- Use the property: sin(-x) = -sin(x)
  rw [show sin (-(π / 12)) = -sin (π / 12) by exact Real.sin_neg (π / 12)]
  ring_nf
  -- Reduce the problem to proving: 2 * sin(π/12) * cos(π/12) = 1/2
  suffices 2 * sin (π * (1 / 12)) * cos (π * (1 / 12)) = 1 / 2 by linarith
  -- Use the double angle formula: sin(2x) = 2sin(x)cos(x)
  rw [show 2 * sin (π * (1 / 12)) * cos (π * (1 / 12)) = sin (2 * (π * (1 / 12))) by exact Eq.symm (sin_two_mul (π * (1 / 12)))]
  ring_nf
  -- Simplify π * (1/6) to π/6
  rw [show π * (1 / 6) = π / 6 by ring_nf]
  -- Complete the proof using the known value of sin(π/6) = 1/2
  exact sin_pi_div_six
