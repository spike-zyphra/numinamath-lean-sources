import Mathlib

open Finset

/- a) The sum of the first \( n \) natural numbers is given by the formula \( \sum_{j=1}^{n} j = 1 + 2 + 3 + \cdots + n = \frac{n(n+1)}{2} \). -/
theorem number_theory_4464_1 (n : ℕ) : ∑ j ∈ range n, ((j + 1) : ℚ) = n * (n + 1) / (2 : ℚ) := by
-- 1. **Base Case**: For \( n = 1 \):
--    \[
--    \sum_{j=1}^{1} j = 1 = \frac{1(1+1)}{2} = 1.
--    \]
--    The base case holds.

-- 2. **Inductive Step**: Assume the formula holds for \( n = k \):
--    \[
--    \sum_{j=1}^{k} j = \frac{k(k+1)}{2}.
--    \]
--    We need to show it holds for \( n = k + 1 \):
--    \[
--    \sum_{j=1}^{k+1} j = \sum_{j=1}^{k} j + (k + 1) = \frac{k(k+1)}{2} + (k + 1).
--    \]
--    Simplifying the right-hand side:
--    \[
--    = \frac{k(k+1) + 2(k + 1)}{2} = \frac{(k + 1)(k + 2)}{2}.
--    \]
--    Thus, the formula holds for \( n = k + 1 \).

-- 3. By induction, the formula is proven for all \( n \).
  induction' n with n ih
  . simp
  . rw [sum_range_succ, ih]
    field_simp
    ring

/- b) The sum of the squares of the first \( n \) natural numbers is given by the formula \( \sum_{j=1}^{n} j^{2} = 1^{2} + 2^{2} + 3^{2} + \cdots + n^{2} = \frac{n(n+1)(2n+1)}{6} \). -/
theorem number_theory_4464_2 (n : ℕ) : ∑ j ∈ range n, ((j + 1) : ℚ) ^ 2 = n * (n + 1) * (2*n + 1) / (6 : ℚ) := by
-- 1. **Base Case**: For \( n = 1 \):
--    \[
--    \sum_{j=1}^{1} j^{2} = 1^{2} = 1 = \frac{1(1+1)(2 \cdot 1 + 1)}{6} = 1.
--    \]
--    The base case holds.

-- 2. **Inductive Step**: Assume the formula holds for \( n = k \):
--    \[
--    \sum_{j=1}^{k} j^{2} = \frac{k(k+1)(2k+1)}{6}.
--    \]
--    We need to show it holds for \( n = k + 1 \):
--    \[
--    \sum_{j=1}^{k+1} j^{2} = \sum_{j=1}^{k} j^{2} + (k + 1)^{2} = \frac{k(k+1)(2k+1)}{6} + (k + 1)^{2}.
--    \]
--    Simplifying the right-hand side:
--    \[
--    = \frac{k(k+1)(2k+1) + 6(k + 1)^{2}}{6} = \frac{(k + 1)(k(2k + 1) + 6(k + 1))}{6}.
--    \]
--    This simplifies to:
--    \[
--    = \frac{(k + 1)(k + 2)(2k + 3)}{6}.
--    \]
--    Thus, the formula holds for \( n = k + 1 \).

-- 3. By induction, the formula is proven for all \( n \).
  induction' n with n ih
  . simp
  . rw [sum_range_succ, ih]
    field_simp
    ring

/- c) The sum of the cubes of the first \( n \) natural numbers is given by the formula \( \sum_{j=1}^{n} j^{3} = 1^{3} + 2^{3} + 3^{3} + \cdots + n^{3} = \left[\frac{n(n+1)}{2}\right]^{2} \). -/
theorem number_theory_4464_3 (n : ℕ) : ∑ j ∈ range n, ((j + 1) : ℚ) ^ 3 = (n * (n + 1) / (2 : ℚ))^2 := by
-- 1. **Base Case**: For \( n = 1 \):
--    \[
--    \sum_{j=1}^{1} j^{3} = 1^{3} = 1 = \left[\frac{1(1+1)}{2}\right]^{2} = 1.
--    \]
--    The base case holds.

-- 2. **Inductive Step**: Assume the formula holds for \( n = k \):
--    \[
--    \sum_{j=1}^{k} j^{3} = \left[\frac{k(k+1)}{2}\right]^{2}.
--    \]
--    We need to show it holds for \( n = k + 1 \):
--    \[
--    \sum_{j=1}^{k+1} j^{3} = \sum_{j=1}^{k} j^{3} + (k + 1)^{3} = \left[\frac{k(k+1)}{2}\right]^{2} + (k + 1)^{3}.
--    \]
--    Factoring out \( (k + 1)^{2} \):
--    \[
--    = (k + 1)^{2} \left[\left(\frac{k(k+1)}{2}\right)^{2} + (k + 1)\right].
--    \]
--    This simplifies to:
--    \[
--    = (k + 1)^{2} \left[\frac{k^{2}(k + 1)^{2}}{4} + (k + 1)\right] = (k + 1)^{2} \left[\frac{k^{2}(k + 1) + 4(k + 1)}{4}\right].
--    \]
--    Thus, we can show that:
--    \[
--    = \left[\frac{(k + 1)(k + 2)}{2}\right]^{2}.
--    \]
--    Therefore, the formula holds for \( n = k + 1 \).

-- 3. By induction, the formula is proven for all \( n \).
  induction' n with n ih
  . simp
  . rw [sum_range_succ, ih]
    field_simp
    ring
