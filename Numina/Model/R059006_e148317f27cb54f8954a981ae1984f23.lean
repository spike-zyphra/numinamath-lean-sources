import Mathlib

theorem algebra_252322 {a r : ℝ} (hr : r ≠ 0) (h1 : a + a * r = 7) (h2 : a + a * r + a * r^2 + a * r^3 + a * r^4 + a * r^5 = 91) :
    a + a * r + a * r^2 + a * r^3 = 28 := by
  -- We can factor the sum of six terms as (a + a * r) * (1 + r^2 + r^4) = 91
  have h3 : a + a * r + a * r^2 + a * r^3 + a * r^4 + a * r^5 = (a + a * r) * (1 + r^2 + r^4) := by
    ring
  rw [h3] at h2
  rw [h1] at h2
  -- Now we compute $7 \cdot (1 + r^2 + r^4) = 91$, so $1 + r^2 + r^4 = 13$
  have h4 : 1 + r^2 + r^4 = 13 := by
    nlinarith
  -- The quadratic in terms of $r^2$ is $1 + y + y^2 = 13$ where $y = r^2$, which leads to $y^2 + y - 12 = 0$.
  have h5 : (r^2 - 3) * (r^2 + 4) = 0 := by
    nlinarith [sq_nonneg (r^2 - 3), sq_nonneg (r^2 + 4)]
  have h6 : r^2 - 3 = 0 := by
    cases' (mul_eq_zero.mp h5) with h7 h8
    · -- Case: r^2 - 3 = 0, so that's our answer
      nlinarith
    · -- Case: r^2 + 4 = 0, which is impossible in real numbers
      have h8' : r^2 + 4 = 0 := by
        nlinarith
      have h9 : r^2 ≥ 0 := sq_nonneg r
      nlinarith
  -- Therefore $r^2 = 3$
  have h8 : r^2 = 3 := by
    linarith
  -- Calculate the sum of the first four terms
  have h9 : a + a * r + a * r^2 + a * r^3 = (a + a * r) * (1 + r^2) := by
    ring
  rw [h9]
  rw [h1, h8]
  -- Now we compute $7 * (1 + 3) = 7 * 4 = 28$
  nlinarith