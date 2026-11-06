import Mathlib

theorem algebra_186702 (x : ℝ) (hx : x^2 - 4 * x + 10 ≠ 0) :
    21 / (x^2 - 4 * x + 10) - x^2 + 4 * x = 6 ↔ x = 3 ∨ x = 1 := by
  constructor
  · -- Forward direction: Equation → roots
    intro h
    have h1 : 21 / (x^2 - 4 * x + 10) - x^2 + 4 * x = 6 := h
    have h2 : (x^2 - 4 * x + 10) ≠ 0 := hx
    field_simp [h2] at h1
    ring_nf at h1
    have eq3 : (x - 3) * (x - 1) = 0 := by 
      nlinarith [sq_nonneg (x ^ 2 - 4 * x + 13), sq_nonneg (x - 3), sq_nonneg (x - 1)]
      -- to factor quartic polynomial into linear factors.
      -- $q(x) = (x^2 - 4x + 3)(x^2 - 4x + 13)$
      -- Then to linear factorization on real numbers, we need fact that
      -- $x^2 - 4x + 13$ has discriminant = 16 - 52 = -26 < 0$ therefore
      -- implies that $x^2 - 4x + 13 = 0$ has no real roots and thus
      -- implying real solutions are x=1, x=3
    cases' (mul_eq_zero.mp eq3) with h4 h5
    · -- Case x = 3
      left
      linarith
    · -- Case x = 1
      right
      linarith
  · -- Backward direction: Roots satisfy Equation
    rintro (h | h)
    · -- Case x = 3
      rw [h]
      norm_num
    · -- Case x = 1
      rw [h]
      norm_num