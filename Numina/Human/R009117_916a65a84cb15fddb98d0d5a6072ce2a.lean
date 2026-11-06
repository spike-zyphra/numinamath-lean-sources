import Mathlib
theorem sequence_evaluation (a : ℕ → ℝ)
(a0 : a 0 = 2)
(arec : ∀ n, a (n + 1) = (a n) / (1 + (a n)))
 : a (2012) = 2 / 4025
 :=
by
  /-
  $\frac{2}{4025}$ Calculating out the first few terms, note that they follow the pattern $a_{n}=\frac{2}{2 n+1}$.
  -/
  have lem : ∀ n, a n = 2 / ((2*n) + 1) := by {
    intro n; induction' n with k ih
    simp; exact a0
    specialize arec k
    rw [arec, ih]
    norm_num; field_simp;
    rw [mul_add]; simp; rw [add_assoc];
    rw [add_assoc]; simp; rw [add_comm]
  }
  /-
  Plugging this back into the recursion shows that it indeed works.
  -/
  specialize arec 2011
  simp at arec
  rw [arec, lem]; simp; field_simp; norm_num
  