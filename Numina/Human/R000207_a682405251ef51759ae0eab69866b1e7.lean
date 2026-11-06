import Mathlib

/- Let  $P_1(x) = x^2 + a_1x + b_1$  and  $P_2(x) = x^2 + a_2x + b_2$  be two quadratic polynomials with integer coeffcients. Suppose  $a_1 \ne a_2$  and there exist integers  $m \ne n$  such that  $P_1(m) = P_2(n), P_2(m) = P_1(n)$ . Prove that  $a_1 - a_2$  is even.-/
theorem number_theory_8564 {a1 a2 b1 b2 : ℤ} {p1 p2 : ℤ → ℤ} (hp1 : ∀ x, p1 x = x ^ 2 + a1 * x + b1)
    (hp2 : ∀ x, p2 x = x ^ 2 + a2 * x + b2) (_ : a1 ≠ a2)
    (hmn : ∃ m n, m ≠ n ∧ p1 m = p2 n ∧ p2 m = p1 n) :
    Even (a1 - a2) := by
  rcases hmn with ⟨m, n, hmn, h1, h2⟩
--   \[
-- P_1(m) = P_2(n)
-- \]
-- \[
-- m^2 + a_1 m + b_1 = n^2 + a_2 n + b_2
-- \]
-- Similarly, from \( P_2(m) = P_1(n) \):
-- \[
-- n^2 + a_1 n + b_1 = m^2 + a_2 m + b_2
-- \]
  rw [hp1, hp2] at h1 h2
--   Expanding and rearranging, we get:
-- \[
-- (m^2 - n^2) + a_1 m - a_2 n + b_1 - b_2 = 0 \quad \dots (1)
-- \]
  replace h1 : (m ^ 2 - n ^ 2) + a1 * m - a2 * n - (b2 - b1) = 0 := by linear_combination h1
--   Rearranging, we get:
-- \[
-- (m^2 - n^2) + a_2 m - a_1 n + b_2 - b_1 = 0 \quad \dots (2)
-- \]
  replace h2 : (m ^ 2 - n ^ 2) + a2 * m - a1 * n + (b2 - b1) = 0 := by linear_combination h2
--   From equations (1) and (2), we have:
-- \[
-- b_2 - b_1 = (m^2 - n^2) + a_1 m - a_2 n = -(m^2 - n^2) - a_2 m + a_1 n
-- \]
  have : (m ^ 2 - n ^ 2) + a1 * m - a2 * n = -(m ^ 2 - n ^ 2) - a2 * m + a1 * n := by linear_combination h1 + h2
-- This implies:
-- \[
-- 2(m^2 - n^2) + m(a_1 + a_2) - n(a_1 + a_2) = 0
-- \]
  have : 2 * (m ^ 2 - n ^ 2) + m * (a1 + a2) - n * (a1 + a2) = 0 := by linear_combination this
--   Therefore:
-- \[
-- 2(m - n)(m + n) + (a_1 + a_2) (m - n) = 0
-- \]
  have : (m - n) * (2 * (m + n) + (a1 + a2)) = 0 := by linear_combination this
--   Since \( m \neq n \), we can divide by \( m - n \) to get:
-- \[
-- 2(m + n) + a_1 + a_2 = 0
-- \]
  rw [mul_eq_zero] at this
  rcases this with h | h
  . have : m = n := by linear_combination h
    contradiction
-- Thus:
-- \[
-- m + n = -\frac{a_1 + a_2}{2}
-- \]
  use -m - n - a2
-- Now, as \( m, n \) are integers, \( m + n \) is also an integer, and
-- \[
-- \frac{a_1 + a_2}{2} \in \mathbb{Z}
-- \]
-- Therefore, \( a_1 + a_2 \) must be an even integer. This is possible only when both \( a_1 \) and \( a_2 \) are even or both are odd. In both cases, we get that \( (a_1 - a_2) \) is always even.
  linear_combination h
