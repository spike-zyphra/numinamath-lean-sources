import Mathlib

/- Calculate $\sqrt{60x} \cdot \sqrt{12x} \cdot \sqrt{63x}$ . Express your answer in simplest radical form in terms of $x$.
Note: When entering a square root with more than one character, you must use parentheses or brackets.  For example, you should enter $\sqrt{14}$ as "sqrt(14)" or "sqrt{14}". -/
theorem algebra_21368 (x : ℝ) (hx : x ≥ 0) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  -- √a√b√c=√(abc)
  have h1: √(60*x) * √(12*x) * √(63*x) = √((60*x)*(12*x)*(63*x)) := by
    have hh1: √((60*x)*(12*x)*(63*x)) = √((60*x)*(12*x)) * √(63*x) := by
      apply Real.sqrt_mul
      apply mul_nonneg (by linarith [hx]) (by linarith [hx])
    have hh2: √((60*x)*(12*x)) = √(60*x) * √(12*x) := by
      apply Real.sqrt_mul (by linarith [hx])
    rw [hh1, hh2]
  -- 60x 12x 63x = (60 12 63) x^3
  have h2: (60*x)*(12*x)*(63*x) = (60*12*63) * x^2 * x := by ring
  -- notice that 60 = 2^2x3x5, 12 = 2^2x3, 63 = 3^2x7,
  -- so 60 12 63 = 4^2x9^2 x 5x7
  have h3: (60*12*63) * x^2 * x = (36*x)^2 * (35*x) := by ring
  -- so it simplifies to 36x √(35x)
  rw [h1, h2, h3]
  rw [Real.sqrt_mul (sq_nonneg (36*x))]
  have: 0 ≤ 36*x := by linarith [hx]
  rw [Real.sqrt_sq this]