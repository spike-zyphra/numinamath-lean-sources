import Mathlib

theorem algebra_319533 (x y z a : ℝ) (ha : a > 0) (h1 : x + y + z = a)
    (h2 : x^2 + y^2 + z^2 = a^2 / 2) :
    ¬(x < 0 ∨ y < 0 ∨ z < 0) ∧ ¬(x > 2 * a / 3 ∨ y > 2 * a / 3 ∨ z > 2 * a / 3) ∧
    ¬(x = y ∧ y = z) := by
  constructor
  · -- Assume some variable is negative
    intro h
    rcases h with h | h | h
    · -- Assume $x < 0$
      nlinarith [sq_nonneg (x), sq_nonneg (y - z), sq_nonneg (y + z - a + x), sq_pos_of_pos ha]
    · -- Assume $y < 0$
      nlinarith [sq_nonneg (y), sq_nonneg (x - z), sq_nonneg (x + z - a + y), sq_pos_of_pos ha]
    · -- Assume $z < 0$
      nlinarith [sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x + y - a + z), sq_pos_of_pos ha]
  constructor
  · -- Assume some variable exceeds $2a/3$
    intro h
    rcases h with h | h | h
    · -- Assume $x > 2a/3$
      nlinarith [sq_nonneg (x - 2 * a / 3), sq_nonneg (y - z), sq_nonneg (y + z - a + x), sq_pos_of_pos ha]
    · -- Assume $y > 2a/3$
      nlinarith [sq_nonneg (y - 2 * a / 3), sq_nonneg (x - z), sq_nonneg (x + z - a + y), sq_pos_of_pos ha]
    · -- Assume $z > 2a/3$
      nlinarith [sq_nonneg (z - 2 * a / 3), sq_nonneg (x - y), sq_nonneg (x + y - a + z), sq_pos_of_pos ha]
  · -- Assume all variables are equal
    intro h
    rcases h with ⟨h12, h23⟩
    have h13 : x = z := by linarith
    nlinarith [sq_nonneg (x - a / 3), sq_nonneg (a), sq_pos_of_pos ha]