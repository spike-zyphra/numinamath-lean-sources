import Mathlib

open Real Set

theorem inequalities_604707
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a * b + b * c + 1 / (c * a)) * (b * c + c * a + 1 / (a * b)) *
    (c * a + a * b + 1 / (b * c)) ≥ (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) := by

  -- First step: simplify reciprocal expressions.
  -- Prove 1/(c*a) = b, because 1/(c*a) * a*b*c = b.
  have h1 : 1 / (c * a) = b := by
    have h2 : c * a * b = 1 := by
      calc
        c * a * b = (a * b * c) := by ring
        _ = 1 := habc
    have h3 : c * a ≠ 0 := by
      nlinarith
    field_simp [h3]
    <;> nlinarith

  -- Prove 1/(a*b) = c, because 1/(a*b) * a*b*c = c.
  have h2 : 1 / (a * b) = c := by
    have h3 : a * b * c = 1 := habc
    have h4 : a * b ≠ 0 := by
      nlinarith
    field_simp [h4]
    <;> nlinarith

  -- Prove 1/(b*c) = a, because 1/(b*c) * a*b*c = a.
  have h3 : 1 / (b * c) = a := by
    have h4 : b * c * a = 1 := by
      calc
        b * c * a = (a * b * c) := by ring
        _ = 1 := habc
    have h5 : b * c ≠ 0 := by
      nlinarith
    field_simp [h5]
    <;> nlinarith

  -- Second step: rewrite the original inequality with simplified expressions
  have h4 : (a * b + b * c + 1 / (c * a)) = b * (a + c + 1) := by
    rw [h1]
    ring

  have h5 : (b * c + c * a + 1 / (a * b)) = c * (a + b + 1) := by
    rw [h2]
    ring

  have h6 : (c * a + a * b + 1 / (b * c)) = a * (b + c + 1) := by
    rw [h3]
    ring

  rw [h4, h5, h6]

  -- Prove that (b(a+b+1))(c(a+b+1))(a(b+c+1)) ≥ (1+2a)(1+2b)(1+2c).
  -- Since a * B * c = 1, the left side simplifies to (1+a+b)(1+b+c)(1+a+c), it expands for comparison.

  -- Final step: Use nonlinear arithmetic solver in Lean 4
  -- But to multiply further expression with positivity
  have pos1 : 0 < a := ha
  have pos2 : 0 < b := hb
  have pos3 : 0 < c := hc
  have pos4 : 0 < a * b := by positivity
  have pos5 : 0 < b * c := by positivity
  have pos6 : 0 < c * a := by positivity

  -- Multiplication tactic in Lean 4
  -- The solver needs squared terms to satisfy greater or equal with positivity
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]