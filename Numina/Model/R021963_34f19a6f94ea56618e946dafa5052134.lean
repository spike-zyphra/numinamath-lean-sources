import Mathlib

theorem algebra_289039 (x y z a : ℝ) (ha : a > 0)
    (h1 : x + y + z = a) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = a ^ 2 / 2) :
    ¬(x < 0) ∧ ¬(y < 0) ∧ ¬(z < 0) ∧ ¬(x > 2 * a / 3) ∧ ¬(y > 2 * a / 3) ∧ ¬(z > 2 * a / 3) := by
  constructor
  · -- Assume x < 0 leads to a contradiction
    intro h
    nlinarith [sq_nonneg (x + y + z - a), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      sq_nonneg (x), sq_nonneg (y), sq_nonneg (z),
      mul_pos ha (show 0 < a by linarith)]
  constructor
  · -- Assume y < 0 leads to a contradiction
    intro h
    nlinarith [sq_nonneg (x + y + z - a), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      sq_nonneg (x), sq_nonneg (y), sq_nonneg (z),
      mul_pos ha (show 0 < a by linarith)]
  constructor
  · -- Assume z < 0 leads to a contradiction
    intro h
    nlinarith [sq_nonneg (x + y + z - a), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      sq_nonneg (x), sq_nonneg (y), sq_nonneg (z),
      mul_pos ha (show 0 < a by linarith)]
  constructor
  · -- Assume x > 2*a/3 leads to a contradiction
    intro h
    nlinarith [sq_nonneg (x + y + z - a), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      sq_nonneg (x - 2 * a / 3), sq_nonneg (y), sq_nonneg (z),
      mul_pos ha (show 0 < a by linarith)]
  constructor
  · -- Assume y > 2*a/3 leads to a contradiction
    intro h
    nlinarith [sq_nonneg (x + y + z - a), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      sq_nonneg (y - 2 * a / 3), sq_nonneg (x), sq_nonneg (z),
      mul_pos ha (show 0 < a by linarith)]
  · -- Assume z > 2*a/3 leads to a contradiction
    intro h
    nlinarith [sq_nonneg (x + y + z - a), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      sq_nonneg (z - 2 * a / 3), sq_nonneg (x), sq_nonneg (y),
      mul_pos ha (show 0 < a by linarith)]