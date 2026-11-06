import Mathlib

/- If \( a \) and \( r \) are real numbers and \( r \neq 1 \), then
\[
\sum_{j=0}^{n} a r^{j} = a + a r + a r^{2} + \cdots + a r^{n} = \frac{a r^{n+1} - a}{r - 1}
\]-/
theorem number_theory_4462
(a r : ℝ)
(h₀ : r ≠ 1)
(n : ℕ) :
(∑ j in Finset.range (n + 1), a * r ^ j) = (a * r ^ (n + 1) - a) / (r - 1) := by
  -- show `r-1≠0` so that `field_simp` can work
  have : r - 1 ≠ 0 := fun h => by rw [sub_eq_zero] at h; exact h₀ h
  -- use mathematical induction
  induction' n with n ih
  -- check the base case
  . field_simp; ring
  -- use induction hypothesis and draw conclusion after simple calculation
  . rw [Finset.sum_range_succ, ih]; field_simp; ring
