import Mathlib

theorem algebra_166137 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h : a^3 * (b - c) + b^3 * (c - a) + c^3 * (a - b) +
      10 * (a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b)) = 0) :
    a + b + c = -10 := by

  have eq1 : (a - b) * (a - c) * (b - c) ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    · -- Show (a - b) ≠ 0
      intro h1
      apply ha
      linarith
    · -- Show (a - c) ≠ 0
      intro h1
      apply hc
      linarith
    · -- Show (b - c) ≠ 0
      intro h1
      apply hb
      linarith

  have eq2 : a^3 * (b - c) + b^3 * (c - a) + c^3 * (a - b) +
      10 * (a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b)) =
      (a + b + c + 10) * ( (a - b) * (a - c) * (b - c) ) := by
    ring_nf

  rw [eq2] at h

  cases' (mul_eq_zero.mp h) with h2 h3
  · -- Case h2 : a + b + c + 10 = 0
    linarith
  · -- Case h3 : (a - b) * (a - c) * (b - c) = 0
    exfalso
    exact eq1 (by
      simpa using h3
    )