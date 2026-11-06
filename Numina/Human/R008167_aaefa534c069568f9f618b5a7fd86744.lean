import Mathlib

/-- Quadratic polynomials P(x) and Q(x)
    have leading coefficients 2 and −2, respectively.
    The graphs of both polynomials pass through the two points (16,54) and (20,53).
    Find P(0)+Q(0). -/
theorem algebra_98593 {P Q : ℝ → ℝ} {b c d e : ℝ} (hP : P = fun x => 2 * x^2 + b * x + c)
    (hQ : Q = fun x => -2 * x^2 + d * x + e) (hP1 : P 16 = 54) (hP2 : P 20 = 53)
    (hQ1 : Q 16 = 54) (hQ2 : Q 20 = 53) :
    P 0 + Q 0 = 116 := by
  -- Let P(x) = 2x^2 +bx + c, Q(x) = -2x^2 + dx + e.
  -- Then P(x) + Q(x) = (b + d) x + c + e.
  have eq_sum (x) : P x + Q x = (b + d) * x + c + e := by
    rw[hP, hQ]
    ring
  -- Hence 108 = 54 + 54 = P(16) + Q(16) = 16 (b+d) + c + e,
  have eq_16 := hP1 ▸ hQ1 ▸ eq_sum 16
  -- such that c + e = 108 - 16(b+d).
  have ce : (c + e) = 108 - 16 * (b + d) := by linarith
  -- Also 106 = 53 + 53 = P(20) + Q(20) = 20 (b+d) + c + e,
  have eq_20 := hP2 ▸ hQ2 ▸ eq_sum 20
  -- such that 4(b+d) = -2,
  rw[add_assoc, ce] at eq_20
  -- hence b+d = -1/2, c + e = 116 = P(0) + Q(0).
  have bd : (b + d) = - 1/2 := by linarith
  rw[eq_sum 0, bd, add_assoc, ce, bd]
  norm_num